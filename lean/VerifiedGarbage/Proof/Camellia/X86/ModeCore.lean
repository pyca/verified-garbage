module

public import VerifiedGarbage.Proof.Camellia.X86.Ecb
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.Camellia.X86.Modes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Camellia.X86.Crypt8
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Camellia.X86.PreparedVerified
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Camellia.X86.Lit
public import VerifiedGarbage.Impl.Camellia.X86.Prepared
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Camellia.X86.Keys
public import VerifiedGarbage.Proof.Camellia.X86.Prologue
public import VerifiedGarbage.Proof.Framework.X86.TaintMono

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
region (`RArg`), where `crypt` reads it again. `crypt` calls
`vg_camellia_crypt_prepared` (`WP.callWith`, with its contract on x86,
`cryptX86`), in a frame of its arguments: the frame and the call's return
address are the core's 16 bytes of stack, apart from the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (argOp sb st movS slotAt movR movI)
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
    (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 1), 4⟩ r) ∧ (∀ r ∈ s.wr, Region.Disjoint ⟨s.ea (argOp 1), 4⟩ r) ∧
    (∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .esp) 16) r) ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨s.ea (argOp 1), 4⟩

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
  obtain ⟨p, hin0, hp, hin1, hR, hRv, hws, hsch, hfit, hdis, hd0, hd1, hdw, hst, hsa⟩ := h
  have hea : ∀ i, s'.ea (argOp i) = s.ea (argOp i) := fun i => by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin0, ?_, by rw [hrd, hwr, hea]; exact hin1, ?_, hRv, ?_,
    by rw [hrd, hwr]; exact hsch, hfit, hdis, by rw [hea]; exact hd0, by rw [hea]; exact hd1,
    by rw [hwr, hea]; exact hdw, by rw [hesp]; exact hst, by rw [hesp, hea]; exact hsa⟩
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
  obtain ⟨p, hin0, hp, hin1, hRa, hRv, hws, hsch, hfit, hdis, hd0, -, hdw, -, -⟩ := hk
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

/-- The cipher on a block in memory: its block function. -/
theorem dirCipher_blockFn (d : Dir) (K : Spec.Camellia.Subkeys) (m : Mem) (p : Addr) :
    dirCipher d K (Spec.Aes.bytesAt m p 16) =
      (Proof.Camellia.blockFn K (specDir d) (Spec.Camellia.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Camellia.cipher, bytesAt_eq_blockAt, ofFn_toList]; rfl
  · rw [dirCipher, Spec.Camellia.invCipher, bytesAt_eq_blockAt, ofFn_toList]; rfl

/-- The table, as `vg_camellia_crypt_prepared` reads it. -/
theorem holds_of_ready {d : Dir} {m : Mem} {B : BitVec 32} {R : Nat} {ws : List (BitVec 64)}
    (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) (hR : R = 18 ∨ R = 24)
    (he : ∀ i < 8 * (R / 6) + 2, EntryOk m B i (ws.getD (permOf d (R / 6) i) 0)) :
    Spec.Camellia.Prepared.Holds layout m (B.setWidth 64) R ws (specDir d) :=
  holds_of_words hfit hR (words_of_entries fun e he' => by
    rw [ofSpecDir_specDir, keyEntry_eq]; exact he e he')

theorem ready_of_holds {d : Dir} {m : Mem} {B : BitVec 32} {R : Nat} {ws : List (BitVec 64)}
    (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) (hR : R = 18 ∨ R = 24)
    (h : Spec.Camellia.Prepared.Holds layout m (B.setWidth 64) R ws (specDir d)) :
    ∀ i < 8 * (R / 6) + 2, EntryOk m B i (ws.getD (permOf d (R / 6) i) 0) := fun i hi => by
  have := entries_of_words (words_of_holds hfit hR h) hi
  rwa [ofSpecDir_specDir, keyEntry_eq] at this

/-- The table survives what keeps the bytes outside a batch's ranges. -/
theorem holds_of_keeps {R : Nat} {m m' : Mem} {B : BitVec 32} {w : List (BitVec 64)}
    {d : Spec.Camellia.Direction} (hR : R = 18 ∨ R = 24)
    (h : Spec.Camellia.Prepared.Holds layout m (B.setWidth 64) R w d)
    (hk : Spec.Camellia.Prepared.Keeps (B.setWidth 64) wsWords layout.cryptScratch m m') :
    Spec.Camellia.Prepared.Holds layout m' (B.setWidth 64) R w d := fun r hr i hi => by
  have hg : R / 6 ≤ 4 := by omega
  have hr' := hr
  rw [layout_table] at hr'
  simp only [List.mem_singleton] at hr'; subst hr'
  dsimp only at hi ⊢
  rw [hk (416 + i) (by simp only [wsWords, slots_eq]; omega) (by
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [keySlot_eq, savedSlot_eq, slots_eq]; omega)]
  exact h _ hr i hi

/-- A byte of the scratch buffer is outside the core's stack. -/
theorem byte_stk {m m' : Mem} {E B : BitVec 32} {n o : Nat} {rs : List Region}
    (hf : Frame (rs ++ [stkRegion E 16]) m m') (hrs : ∀ r ∈ rs, Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 o, 1⟩ r)
    (hst : Region.Disjoint (stkRegion E 16) ⟨B.setWidth 64, n⟩) (hfit : B.toNat + n ≤ 2 ^ 32) (ho : o < n) :
    m' (B.setWidth 64 + BitVec.ofNat 64 o) = m (B.setWidth 64 + BitVec.ofNat 64 o) := by
  refine hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact hrs r hr _ (Region.contains_self _ _) hc
  · simp only [List.mem_singleton] at hr; subst hr
    exact hst _ hc (VG.Offset.contains_base _ (by omega) (by
      have := setWidth_toNat B; omega))

theorem crypt_wp (d : Dir) {s : State} {B : BitVec 32} {k : Nat × List (BitVec 64)}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hr : ReadyAt d s.mem B k) (ha : RArg s k.1)
    (hst : Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨B.setWidth 64, 4 * (dirCore d).total⟩)
    (hsa : Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨s.ea (argOp 1), 4⟩)
    (hesp : 16 ≤ (s.gpr .esp).toNat) :
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
  rw [dirCore_total] at hfB hst
  have hfit' : B.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega
  have hst' : Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨B.setWidth 64, 4 * slots⟩ :=
    hst.sub_right (Region.sub_prefix (by rw [slots_eq]; omega))
  have hH := holds_of_ready hfit' hRv he
  -- The arguments.
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax 1 ha.1
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -, -⟩ := movR_ok s₁ .ecx sb
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s₂ .edx (BitVec.ofNat 32 wsWords)
  have g₃ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₃ r h3, o₂ r h2, o₁ r h1]
  have esp₃ : s₃.gpr .esp = s.gpr .esp := g₃ _ (by decide) (by decide) (by decide)
  have eax₃ : s₃.gpr .eax = BitVec.ofNat 32 R := by
    rw [o₃ _ (by decide), o₂ _ (by decide), v₁]; exact ha.2.1
  have ecx₃ : s₃.gpr .ecx = B := by rw [o₃ _ (by decide), v₂, o₁ _ (by decide), hB']
  have mem₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, rd₁]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  show WP isa cryptCall s _
  unfold cryptCall
  refine WP.seq (WP.of_runBlock ⟨s₃, ?_, ?_⟩)
  · rw [show ([.mov .eax (.mem (argOp 1)), movR .ecx sb, movI .edx (BitVec.ofNat 32 wsWords)] : List Instr) =
      [.mov .eax (.mem (argOp 1))] ++ ([movR .ecx sb] ++ [movI .edx (BitVec.ofNat 32 wsWords)]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  -- The call.
  have hrs : Reg.esp ∉ [Reg.edx, .ecx, .eax] := by decide
  have hfit₃ : 4 * [Reg.edx, .ecx, .eax].length + 4 ≤ (s₃.gpr .esp).toNat := by
    rw [esp₃]; show 16 ≤ _; omega
  have a0 : arg (pushed [.edx, .ecx, .eax] s₃).callEntry 0 = BitVec.ofNat 32 R := by
    rw [callEntry_arg hfit₃ hrs (i := 0) (by decide)]; exact eax₃
  have a1 : arg (pushed [.edx, .ecx, .eax] s₃).callEntry 1 = B := by
    rw [callEntry_arg hfit₃ hrs (i := 1) (by decide)]; exact ecx₃
  have a2 : arg (pushed [.edx, .ecx, .eax] s₃).callEntry 2 = BitVec.ofNat 32 wsWords := by
    rw [callEntry_arg hfit₃ hrs (i := 2) (by decide)]; exact v₃
  have cE := callEntry_frame hfit₃ hrs
  rw [show 4 * [Reg.edx, .ecx, .eax].length + 4 = 16 from rfl, esp₃, mem₃] at cE
  have cE' : Frame ([] ++ [stkRegion (s.gpr .esp) 16]) s.mem (pushed [.edx, .ecx, .eax] s₃).callEntry.mem := cE
  have hHC : Spec.Camellia.Prepared.Holds layout (pushed [.edx, .ecx, .eax] s₃).callEntry.mem (B.setWidth 64) R ws (specDir d) := fun r hr i hi => by
    have hg : R / 6 ≤ 4 := by omega
    have hr' := hr
    rw [layout_table] at hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    dsimp only at hi ⊢
    rw [byte_stk cE' (fun _ h => (List.not_mem_nil h).elim) hst' hfit' (by rw [slots_eq]; omega)]
    exact hH _ hr i hi
  have wsN : (BitVec.ofNat 32 wsWords).toNat = 336 := rfl
  have argsC : argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 12).setWidth 64 := by
    rw [callEntry_argAddr0, esp₃]; rfl
  have espC : ((pushed [.edx, .ecx, .eax] s₃).callEntry.gpr .esp).toNat = (s.gpr .esp).toNat - 16 := by
    rw [callEntry_espNat hfit₃, esp₃]; rfl
  have espC' : ((pushed [.edx, .ecx, .eax] s₃).callEntry.gpr .esp).setWidth 64 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_esp', esp₃]; rfl
  have hstk : stkRegion (s.gpr .esp) 16 = below (s.gpr .esp) 16 := rfl
  have argsSub : Region.Sub ⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩ (stkRegion (s.gpr .esp) 16) := by
    rw [argsC, hstk]; exact below_sub (by omega) hesp
  have hst2 : Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨B.setWidth 64, 336 * 8⟩ := by
    have := hst'; rw [slots_eq] at this; exact this
  have hR32 : R < 2 ^ 32 := by omega
  have scrIn : (⟨B.setWidth 64, 4 * (dirCore d).total⟩ : Region) ∈ s₃.wr := by rw [wr₃']; exact hs.wr
  refine WP.callWith (k := cryptX86) crypt_correct crypt_noSp (by decide) hrs
    (by rw [crypt_stackUse, esp₃]; show 16 ≤ _; omega)
    (rd := [⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩]) (wr := [⟨B.setWidth 64, 336 * 8⟩])
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ fun s' rd' wr' cs f ⟨s₂, m₂, post⟩ => ?_
  · rw [State.withRegions_rd, argAddr_withRegions]
  · rw [State.withRegions_wr, arg_withRegions, arg_withRegions, a1, a2]; rfl
  · rw [argAddr_withRegions, arg_withRegions, arg_withRegions, a1, a2]
    exact (hst2.sub_left argsSub)
  · rw [State.withRegions_gpr, arg_withRegions, arg_withRegions, a1, a2, espC']
    exact (hst2.sub_left (Region.sub_prefix (by decide)))
  · rw [arg_withRegions, arg_withRegions, a1, a2, wsN]; rw [slots_eq] at hfit'; omega
  · rw [State.withRegions_gpr, espC]; have := (s.gpr .esp).isLt; omega
  · rw [arg_withRegions, a0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR32]; exact hRv
  · rw [arg_withRegions, a2, wsN, size_eq, slots_eq]
  · refine ⟨ws, specDir d, ?_⟩
    rw [arg_withRegions, arg_withRegions, a0, a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR32, State.withRegions_mem]
    exact hHC
  · refine Covers.append_left (Covers.right (Covers.of_mem fun r hr => ?_)) (Covers.right ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [argsC, ← esp₃]; exact List.mem_cons_self
    · exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ scrIn, 0, by rw [BitVec.add_zero],
          by show 0 + 336 * 8 ≤ 4 * (dirCore d).total; rw [dirCore_total]; omega⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ scrIn, 0, by rw [BitVec.add_zero],
      by show 0 + 336 * 8 ≤ 4 * (dirCore d).total; rw [dirCore_total]; omega⟩
  -- After the call.
  have hHC' : Spec.Camellia.Prepared.Holds layout
      ((pushed [.edx, .ecx, .eax] s₃).callEntry.withRegions [⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩]
        [⟨B.setWidth 64, 336 * 8⟩]).mem
      ((arg ((pushed [.edx, .ecx, .eax] s₃).callEntry.withRegions [⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩]
        [⟨B.setWidth 64, 336 * 8⟩]) 1).setWidth 64)
      (arg ((pushed [.edx, .ecx, .eax] s₃).callEntry.withRegions [⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩]
        [⟨B.setWidth 64, 336 * 8⟩]) 0).toNat ws (specDir d) := by
    rw [arg_withRegions, arg_withRegions, a0, a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR32, State.withRegions_mem]
    exact hHC
  have hE := post.1 ws (specDir d) hHC'
  have hK := post.2
  simp only [arg_withRegions, a0, a1, a2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR32, State.withRegions_mem,
    m₂] at hE hK
  rw [show wsWords % 2 ^ 32 = wsWords from rfl] at hK
  have hH' : Spec.Camellia.Prepared.Holds layout s'.mem (B.setWidth 64) R ws (specDir d) :=
    holds_of_keeps hRv hHC hK
  have espS : s'.gpr .esp = s.gpr .esp := by rw [cs .esp (by decide), esp₃]
  have fS : Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem := by
    rw [← mem₃]
    refine f.sub fun r hr => ?_
    rw [crypt_stackUse] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by simp only [coreRegion]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
        rw [esp₃]; exact fun _ h => h⟩
  refine ⟨by rw [show VG.Impl.Modes.X86.sb = .edi from rfl, cs .edi (by decide)]; rw [g₃ _ (by decide)
      (by decide) (by decide)]; exact hB', espS,
    ⟨⟨hRv, ready_of_holds hfit' hRv hH'⟩, ⟨by rw [rd', wr', ea_arg espS, rd₃', wr₃', ← ea_arg (rfl)]; exact ha.1,
      ?_, by rw [wr', ea_arg espS, wr₃', ← ea_arg rfl]; exact ha.2.2⟩⟩, fS, fun j hj => ?_,
    by rw [rd', rd₃'], by rw [wr', wr₃']⟩
  · rw [ea_arg espS, ← ea_arg (s₀ := s) rfl]
    rw [fS.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact ha.2.1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (ha.2.2 _ hs.wr).sub_right (Region.sub_prefix (by simp only [dirCore_total, dirCore_slots]; omega))
      · exact hsa.symm
  · have hj8 : j < 8 := hj
    have ha' : blkAddr (dirCore d) B j = B.setWidth 64 + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := rfl
    have hb := congrArg (fun l => l[j]?) hE
    rw [Proof.Camellia.ecb_eq] at hb
    simp only [Spec.Camellia.blocksAt, layout, List.getElem?_map, List.getElem?_range hj8, Option.map_some,
      Option.some.injEq] at hb
    rw [dirCore_bw, show 4 * 4 = 16 from rfl, dirCipher_blockFn, bytesAt_eq_blockAt, ha']
    simp only [layout]
    have hblk : Spec.Camellia.blockAt (pushed [.edx, .ecx, .eax] s₃).callEntry.mem
        (B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot) + BitVec.ofNat 64 (16 * j)) =
        Spec.Camellia.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot) + BitVec.ofNat 64 (16 * j)) := by
      apply Vector.ext; intro i hi
      simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn, VG.Offset.add_add]
      exact byte_stk cE' (fun _ h => (List.not_mem_nil h).elim) hst' hfit'
        (by rw [slots_eq, tailSlot_eq]; omega)
    rw [hb, hblk]

/-- Camellia's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready s B k := (ReadyAt d s.mem B k ∧ RArg s k.1) ∧ B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32 ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨B.setWidth 64, 4 * (dirCore d).total⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨s.ea (argOp 1), 4⟩
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher, dirCore]
  layout := ⟨by simp only [dirCore]; decide, .inr rfl, by simp only [dirCore, slots_eq, tailSlot_eq]; omega,
    by simp only [dirCore]; omega⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame {_ _ _ k _} h e r w _ hf hs hd := by
    obtain ⟨⟨⟨hR, he⟩, ha⟩, hfit, hst, hsa⟩ := h
    have hg4 : 8 * (k.1 / 6) + 2 ≤ 34 := by omega
    exact ⟨⟨⟨hR, fun i hi => entry_keep hfit hf hd (by omega) (he i hi)⟩, ha.frame e r w hf hs⟩, hfit,
      by rw [e]; exact hst, by rw [e, ea_arg e, ← ea_arg rfl]; exact hsa⟩
  prepare_wp {s _ _ _} hB hs hR hk _ := WP.mono (prepare_wp d hB hs hR hk) fun s' ⟨r, h⟩ => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hst, hsa⟩ := hk
    exact ⟨⟨r, hs.fit, by rw [h.2.1]; exact hst _ hR, by rw [h.2.1, ea_arg h.2.1, ← ea_arg rfl]; exact hsa⟩, h⟩
  crypt_wp hB hs hr hsp := WP.mono (crypt_wp d hB hs hr.1.1 hr.1.2 hr.2.2.1 hr.2.2.2 hsp)
    fun _ ⟨b, e, r, h⟩ => ⟨b, e, ⟨r, hr.2.1, by rw [e]; exact hr.2.2.1, by
      rw [e, ea_arg e, ← ea_arg rfl]; exact hr.2.2.2⟩, h⟩

end VG.Proof.Camellia.X86
