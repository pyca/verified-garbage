module

public import VerifiedGarbage.Proof.Camellia.X86.Ecb
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.Camellia.X86.Modes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Camellia.X86.Crypt8
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# Camellia's core for the modes on x86 (32-bit)

`dirCoreSpec d`: Camellia's core for the direction `d`
(`Impl.Camellia.X86.dirCore d`) meets what the modes need of a core
(`Proof.Modes.X86.CoreSpec`), with the key the number of rounds and the
schedule's words, read through the first two stack arguments, its cipher
`Spec.Camellia.cipher` for encryption and `Spec.Camellia.invCipher` for
decryption under them, and the key ready when the table of subkeys in `d`'s
order for that many rounds is in the scratch buffer (`ReadyAt`) and the
number of rounds is still in its stack argument, apart from every writable
region (`RArg`), where `crypt` reads it again.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (argOp sb st movS slotAt)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)
open VG.Proof.Camellia (schedWords schedWords_getD wordAt_frame bytesAt_eq_blockAt ofFn_toList encryptWith_eq
  decryptWith_eq dirPerm_lt)

/-- The number of rounds and the schedule's words, through the first two
stack arguments, the schedule outside the regions `rs`, as are those
arguments, and the number of rounds outside every writable region. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 ∧ s.mem.readW (s.ea (argOp 0)) 32 = p ∧
    InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4 ∧ s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 k.1 ∧
    (k.1 = 18 ∨ k.1 = 24) ∧ k.2 = schedWords s.mem (p.setWidth 64) k.1 ∧
    (⟨p.setWidth 64, 272⟩ : Region) ∈ s.rd ++ s.wr ∧ p.toNat + 272 ≤ 2 ^ 32 ∧
    (∀ r ∈ rs, Region.Disjoint ⟨p.setWidth 64, 272⟩ r) ∧ (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r) ∧
    (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 1), 4⟩ r) ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨s.ea (argOp 1), 4⟩ r

/-- The table of subkeys in the order of `d` for `k.1` rounds, in the scratch
buffer at `B`. -/
def ReadyAt (d : Dir) (m : Mem) (B : BitVec 32) (k : Nat × List (BitVec 64)) : Prop :=
  (k.1 = 18 ∨ k.1 = 24) ∧ ∀ i < 8 * (k.1 / 6) + 2, EntryOk m B i (k.2.getD (permOf d (k.1 / 6) i) 0)

/-- The number of rounds `R` in the second stack argument, readable and apart
from every writable region. -/
def RArg (s : State) (R : Nat) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4 ∧ s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R ∧
    ∀ r ∈ s.wr, Region.Disjoint ⟨s.ea (argOp 1), 4⟩ r

theorem RArg.frame {s s' : State} {R : Nat} {rs : List Region} (h : RArg s R) (hesp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r') : RArg s' R := by
  obtain ⟨hin, hv, hd⟩ := h
  have hea : s'.ea (argOp 1) = s.ea (argOp 1) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨by rw [hrd, hwr, hea]; exact hin, ?_, by rw [hwr, hea]; exact hd⟩
  rw [hea, hf.readW (Region.contains_self _ _) (fun r hr => by
    obtain ⟨r', hr', hs⟩ := hsub r hr; exact (hd r' hr').sub_right hs) (by decide), hv]

theorem dirCore_slots (d : Dir) : (dirCore d).slots = 672 := rfl
theorem dirCore_total (d : Dir) : (dirCore d).total = 682 := rfl
theorem dirCore_ka (d : Dir) : (dirCore d).ka = 2 := rfl
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 4 := rfl

/-- The scratch buffer of the modes is one for the ECB code. -/
theorem scrIn_of {s : State} {B : BitVec 32} {d : Dir}
    (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total) : ScrIn s.wr B :=
  have hf := hs.fit
  ⟨⟨682, by rw [slots_eq]; decide, hf, hs.wr⟩, by rw [dirCore_total] at hf; rw [slots_eq]; omega⟩

/-- Regions within the core's slots are within the modes' scratch buffer. -/
theorem sub_scr {s : State} {B : BitVec 32} {d : Dir} (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r ⟨B.setWidth 64, 4 * slots⟩) :
    ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r' := fun r hr =>
  ⟨_, hs.wr, sub_trans (h r hr) (Region.sub_prefix (by rw [dirCore_total, slots_eq]; decide))⟩

/-- A word of the core's slots `[lo, hi)`, outside the regions apart from the
core or within its buffer, when those slots are after the buffer. -/
theorem slot_keep_core {d : Dir} {B : BitVec 32} (hfit : B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32)
    {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B))
    {k : Nat} (hk1 : tailSlot + 32 ≤ k) (hk2 : k < slots) :
    m'.readW (wordAddr B k) 32 = m.readW (wordAddr B k) 32 := by
  rw [dirCore_total] at hfit
  rw [slots_eq] at hk2
  rw [slot_addr (by omega)]
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases hd r hr with h | h
  · exact h.symm.sub_right (VG.Offset.sub_base _ (by simp only [dirCore, slots_eq]; omega)) |>.symm
  · refine Region.Disjoint.sub_right ?_ h
    exact VG.Offset.disjoint _ (.inr (by simp only [dirCore, tailSlot_eq] at hk1 ⊢; omega))
      (by omega) (by simp only [dirCore, tailSlot_eq]; omega)

theorem entry_keep {d : Dir} {B : BitVec 32} (hfit : B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32)
    {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B))
    {i : Nat} (hi : i < 34) {k : BitVec 64} (h : EntryOk m B i k) : EntryOk m' B i k :=
  h.congr fun j hj => slot_keep_core hfit hf hd (by rw [keySlot_eq, tailSlot_eq]; omega)
    (by rw [keySlot_eq, slots_eq]; omega)

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin0, hp, hin1, hR, hRv, hws, hsch, hfit, hdis, hd0, hd1, hdw⟩ := h
  have hea : ∀ i, s'.ea (argOp i) = s.ea (argOp i) := fun i => by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin0, ?_, by rw [hrd, hwr, hea]; exact hin1, ?_, hRv, ?_,
    by rw [hrd, hwr]; exact hsch, hfit, hdis, by rw [hea]; exact hd0, by rw [hea]; exact hd1,
    by rw [hwr, hea]; exact hdw⟩
  · rw [hea, hf.readW (Region.contains_self _ _) hd0 (by decide), hp]
  · rw [hea, hf.readW (Region.contains_self _ _) hd1 (by decide), hR]
  · rw [hws]
    simp only [schedWords]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega
    exact (wordAt_frame hf fun r hr => (hdis r hr).sub_left (VG.Offset.sub_base _ hl)).symm

/-- `cmpRounds`: Z when there are 18 rounds. -/
theorem cmpRounds_z {s : State} {R : Nat} (hR : R = 18 ∨ R = 24) (hin : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4)
    (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R) :
    ∃ s', runBlock isa cmpRounds s = some s' ∧ s'.zf = some (decide (R = 18)) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, z, o, m, rd, wr⟩ := cmpRounds_ok s hin
  refine ⟨s', e, ?_, o, m, rd, wr⟩
  rw [z, hv, show (18 : BitVec 32) = BitVec.ofNat 32 18 from rfl, ofNat32_sub_beq (by omega) (by decide)]

theorem prepare_wp (d : Dir) {s : State} {B : BitVec 32} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hR : (⟨B.setWidth 64, 4 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => (ReadyAt d s'.mem B k ∧ RArg s' k.1) ∧
      s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hin0, hp, hin1, hRa, hRv, hws, hsch, hfit, hdis, hd0, -, hdw⟩ := hk
  simp only at hRa hRv hws ⊢
  have hB' : s.gpr sb = B := hB
  have hw : ScrIn s.wr B := scrIn_of hs
  have hsub : Region.Sub ⟨B.setWidth 64, 4 * slots⟩ ⟨B.setWidth 64, 4 * (dirCore d).total⟩ :=
    Region.sub_prefix (by rw [dirCore_total, slots_eq]; decide)
  -- The number of rounds.
  obtain ⟨s₂, e₂, hz, g₂, mem₂, rd₂, wr₂⟩ := cmpRounds_z hRv hin1 hRa
  have esp₂ : s₂.gpr .esp = s.gpr .esp := g₂ _ (by decide)
  have hsep : Region.Disjoint ⟨p.setWidth 64, 272⟩ ⟨B.setWidth 64, 4 * slots⟩ := (hdis _ hR).sub_right hsub
  have hpre : KeyPre s₂ B p :=
    ⟨by rw [g₂ _ (by decide)]; exact hB', by rw [wr₂]; exact hw, by rw [rd₂, wr₂]; exact hsch, hfit, hsep⟩
  have harg : InRegions (s₂.rd ++ s₂.wr) (s₂.ea (argOp 0)) 4 := by
    rw [rd₂, wr₂, ea_arg esp₂]; exact hin0
  have hparg : s₂.mem.readW (s₂.ea (argOp 0)) 32 = p := by
    rw [ea_arg esp₂, mem₂]; exact hp
  show WP isa (.seq (.block cmpRounds) (.ite .e (keys d 3) (keys d 4))) s _
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  refine WP.mono (M := isa) (Q := KeysPost s₂ B p g (permOf d g))
    (WP.ite (decide (R = 18)) ((eval_e s₂).trans hz) (fun h => ?_) (fun h => ?_)) fun s₃ k₃ => ?_
  · obtain rfl : g = 3 := by simp at h; omega
    exact keys_wp d (Or.inl rfl) hpre harg hparg
  · obtain rfl : g = 4 := by simp at h; omega
    exact keys_wp d (Or.inr rfl) hpre harg hparg
  have b₃ : s₃.gpr sb = B := k₃.pre.base
  have esp₃ : s₃.gpr .esp = s.gpr .esp := by rw [k₃.regs _ (by decide) (by decide), esp₂]
  have f₃ : Frame [⟨B.setWidth 64, 4 * slots⟩] s.mem s₃.mem := by
    rw [← mem₂]
    exact k₃.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact table_sub_scr⟩
  refine ⟨⟨⟨hRv, fun i hi => ?_⟩, RArg.frame ⟨hin1, hRa, hdw⟩ esp₃ (by rw [k₃.rd, rd₂]) (by rw [k₃.wr, wr₂]) f₃
      (sub_scr hs fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h)⟩,
    b₃, esp₃, ?_, by rw [k₃.rd, rd₂], by rw [k₃.wr, wr₂]⟩
  · rw [hgR] at hi ⊢
    have hpl : permOf d g i < 8 * g + 2 := dirPerm_lt (specDir d) hi
    have hl : permOf d g i < Spec.Camellia.scheduleLength R := by
      simp only [Spec.Camellia.scheduleLength]; omega
    have := k₃.ent i hi
    rw [mem₂] at this
    rw [hws, schedWords_getD _ _ hl]
    exact this
  · exact f₃.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self,
      fun _ h => h⟩

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

theorem crypt_wp (d : Dir) {s : State} {B : BitVec 32} {k : Nat × List (BitVec 64)}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hr : ReadyAt d s.mem B k) (ha : RArg s k.1) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      (ReadyAt d s'.mem B k ∧ RArg s' k.1) ∧
      Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨hRv, he⟩ := hr
  simp only at hRv he ha ⊢
  have hB' : s.gpr sb = B := hB
  have hfB := hs.fit
  rw [dirCore_total] at hfB
  have hfit' : B.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega
  have hw : ScrIn s.wr B := scrIn_of hs
  -- The number of rounds.
  obtain ⟨s₂, e₂, hz, g₂, mem₂, rd₂, wr₂⟩ := cmpRounds_z hRv ha.1 ha.2.1
  have b₂ : s₂.gpr sb = B := by rw [g₂ _ (by decide)]; exact hB'
  show WP isa (.seq (.block cmpRounds) (.ite .e (crypt8 3) (crypt8 4))) s _
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  rw [hgR] at he
  let E : Nat → BitVec 64 := fun i => ws.getD (permOf d g i) 0
  have hcore : CorePre s₂ g E :=
    { scr := by rw [b₂, wr₂]; exact hw
      nk34 := by omega
      keys := fun i hi => by rw [b₂, mem₂]; exact he i hi
      hg := hg }
  refine WP.mono (M := isa) (Q := fun s' => Ctx s₂ s' ∧ ∀ b < 8, blk s' b =
      Spec.Camellia.encodeBlock (cryptWords g E (Spec.Camellia.decodeBlock (blk s₂ b))))
    (WP.ite (decide (R = 18)) ((eval_e s₂).trans hz) (fun h => ?_) (fun h => ?_)) fun s₃ ⟨c₃, b₃⟩ => ?_
  · obtain rfl : g = 3 := by simp at h; omega
    exact crypt8_ok hcore
  · obtain rfl : g = 4 := by simp at h; omega
    exact crypt8_ok hcore
  have base₃ : s₃.gpr sb = B := by rw [c₃.base, b₂]
  have esp₃ : s₃.gpr .esp = s.gpr .esp := by rw [c₃.keep _ (by decide) (by decide), g₂ _ (by decide)]
  have f₃ : Frame (ctxRegions B) s.mem s₃.mem := by have := c₃.frame; rw [b₂, mem₂] at this; exact this
  have ctxSub : ∀ r ∈ ctxRegions B, Region.Sub r ⟨B.setWidth 64, 4 * slots⟩ := fun r hr => by
    simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by rw [keySlot_eq, slots_eq]; decide)
    · exact slot_sub hfit' (by rw [grpSlot_eq, slots_eq]; decide)
  have dT := ctx_disj hfit'
  have keep : ∀ k, keySlot ≤ k → k < grpSlot → s₃.mem.readW (wordAddr B k) 32 = s.mem.readW (wordAddr B k) 32 :=
    fun k h1 h2 => slot_keep hfit' (by decide) f₃ dT h1 h2
  refine ⟨base₃, esp₃, ⟨⟨hRv, fun i hi => ?_⟩,
      RArg.frame ha esp₃ (by rw [c₃.rd, rd₂]) (by rw [c₃.wr, wr₂]) f₃ (sub_scr hs ctxSub)⟩, ?_,
    fun j hj => ?_, by rw [c₃.rd, rd₂], by rw [c₃.wr, wr₂]⟩
  · have hg4 : 8 * g + 2 ≤ 34 := by omega
    rw [hgR] at hi ⊢
    exact (he i hi).congr fun j hj => keep _ (by omega) (by rw [keySlot_eq, grpSlot_eq]; omega)
  · exact f₃.sub fun r hr => ⟨_, List.mem_cons_self, ctxSub r hr⟩
  · have hj8 : j < 8 := hj
    have ha' : blkAddr (dirCore d) B j = B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j) := by
      simp only [blkAddr, slotA, dirCore, VG.Offset.add_add]
    have e5 := b₃ j hj8
    simp only [blk, base₃, b₂, mem₂] at e5
    rw [dirCore_bw, ha', dirCipher_bytes d hRv, bytesAt_eq_blockAt, e5, hgR]

/-- Camellia's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready s B k := (ReadyAt d s.mem B k ∧ RArg s k.1) ∧ B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher, dirCore]
  layout := ⟨by simp only [dirCore]; decide, .inr rfl, by simp only [dirCore, slots_eq, tailSlot_eq]; omega,
    by simp only [dirCore]; omega⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame {_ _ _ k _} h e r w _ hf hs hd := by
    obtain ⟨⟨⟨hR, he⟩, ha⟩, hfit⟩ := h
    have hg4 : 8 * (k.1 / 6) + 2 ≤ 34 := by omega
    exact ⟨⟨⟨hR, fun i hi => entry_keep hfit hf hd (by omega) (he i hi)⟩, ha.frame e r w hf hs⟩, hfit⟩
  prepare_wp hB hs hR hk _ := WP.mono (prepare_wp d hB hs hR hk) fun _ ⟨r, h⟩ => ⟨⟨r, hs.fit⟩, h⟩
  crypt_wp hB hs hr _ := WP.mono (crypt_wp d hB hs hr.1.1 hr.1.2) fun _ ⟨b, e, r, h⟩ => ⟨b, e, ⟨r, hr.2⟩, h⟩

end VG.Proof.Camellia.X86
