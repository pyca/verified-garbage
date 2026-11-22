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
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Camellia.X86.Lit
public import VerifiedGarbage.Impl.Camellia.X86.Prepared
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Camellia.X86.PreparedBody
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
`vg_camellia_crypt_prepared` (`cryptCall_wp`, `Call.lean`), in a frame of
its arguments: the frame and the call's return address are the core's 16
bytes of stack, apart from the scratch buffer.
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
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨s.ea (argOp 1), 4⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨p.setWidth 64, 272⟩ ∧
    InRegions (s.rd ++ s.wr) (s.ea (argOp 5)) 4 ∧ (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 5), 4⟩ r) ∧
    (∀ r ∈ rs, r.base = (s.mem.readW (s.ea (argOp 5)) 32).setWidth 64) ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨s.ea (argOp 5), 4⟩

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

theorem dirCore_total (d : Dir) : (dirCore d).total = 682 := rfl
theorem dirCore_ka (d : Dir) : (dirCore d).ka = 2 := rfl
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 4 := rfl

/-- The scratch buffer of the modes is one for the ECB code. -/
theorem scrIn_of {s : State} {B : BitVec 32} {d : Dir}
    (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total) : ScrIn s.wr B :=
  have hf := hs.fit
  ⟨⟨682, by rw [slots_eq]; decide, hf, hs.wr⟩, by rw [dirCore_total] at hf; rw [slots_eq]; omega_using [hf]⟩

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
  rw [slot_addr (by omega_using [hfit, hk2])]
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases hd r hr with h | h
  · exact h.symm.sub_right (VG.Offset.sub_base _ (by simp only [dirCore, slots_eq]; omega_using [hk2])) |>.symm
  · refine Region.Disjoint.sub_right ?_ h
    exact VG.Offset.disjoint _ (.inr (by simp only [dirCore, tailSlot_eq] at hk1 ⊢; omega_using [hk1]))
      (by omega_using [hk2]) (by simp only [dirCore, tailSlot_eq]; omega_using [])

theorem entry_keep {d : Dir} {B : BitVec 32} (hfit : B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32)
    {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B))
    {i : Nat} (hi : i < 34) {k : BitVec 64} (h : EntryOk m B i k) : EntryOk m' B i k :=
  h.congr fun j hj => slot_keep_core hfit hf hd (by rw [keySlot_eq, tailSlot_eq]; omega_using [])
    (by rw [keySlot_eq, slots_eq]; omega_using [hi, hj])

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin0, hp, hin1, hR, hRv, hws, hsch, hfit, hdis, hd0, hd1, hdw, hst, hsa, hsk, hin5, hd5, hb5, hs5⟩ := h
  have hea : ∀ i, s'.ea (argOp i) = s.ea (argOp i) := fun i => by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin0, ?_, by rw [hrd, hwr, hea]; exact hin1, ?_, hRv, ?_,
    by rw [hrd, hwr]; exact hsch, hfit, hdis, by rw [hea]; exact hd0, by rw [hea]; exact hd1,
    by rw [hwr, hea]; exact hdw, by rw [hesp]; exact hst, by rw [hesp, hea]; exact hsa, by rw [hesp]; exact hsk,
    by rw [hrd, hwr, hea]; exact hin5, by rw [hea]; exact hd5, fun r hr => ?_, by rw [hesp, hea]; exact hs5⟩
  · rw [hea, hf.readW (Region.contains_self _ _) hd0 (by decide), hp]
  · rw [hea, hf.readW (Region.contains_self _ _) hd1 (by decide), hR]
  · rw [hws]
    simp only [schedWords]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega_using [hRv, hi]
    exact (wordAt_frame hf fun r hr => (hdis r hr).sub_left (VG.Offset.sub_base _ hl)).symm
  · rw [hea, hf.readW (Region.contains_self _ _) hd5 (by decide)]; exact hb5 r hr

theorem prepare_wp (d : Dir) {s : State} {B : BitVec 32} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hR : (⟨B.setWidth 64, 4 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (hesp : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).prepare s fun s' => (ReadyAt d s'.mem B k ∧ RArg s' k.1) ∧
      s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hin0, hp, hin1, hRa, hRv, hws, hsch, hfit, hdis, hd0, -, hdw, hst, hsa, hsk, hin5, hd5, hb5, hs5⟩ := hk
  simp only at hRa hRv hws ⊢
  have hB' : s.gpr sb = B := hB
  have hw : ScrIn s.wr B := scrIn_of hs
  have hsub : Region.Sub ⟨B.setWidth 64, 4 * slots⟩ ⟨B.setWidth 64, 4 * (dirCore d).total⟩ :=
    Region.sub_prefix (by rw [dirCore_total, slots_eq]; decide)
  have hv5 : s.mem.readW (s.ea (argOp 5)) 32 = B := by
    have e := congrArg (BitVec.setWidth 32) (hb5 _ hR)
    simp only [BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq] at e
    exact e.symm
  show WP isa (prepareCall d 5) s _
  refine WP.mono (prepareCall_wp d 5 (R := R) hB' hw hRv hin5 hv5 ((hd5 _ hR).sub_right hsub) hs5.symm hin0 hp hin1 hRa hsch hfit ((hdis _ hR).sub_right hsub)
    hsk.symm ((hst _ hR).sub_right hsub) hesp)
    fun s₃ ⟨b₃, cs₃, rd₃, wr₃, f₃, e₃, _⟩ => ?_
  have esp₃ : s₃.gpr .esp = s.gpr .esp := cs₃ _ (by simp [calleeSaved])
  have f₃' : Frame [⟨B.setWidth 64, 4 * slots⟩, below (s.gpr .esp) 16] s.mem s₃.mem := f₃
  have hea : s₃.ea (argOp 1) = s.ea (argOp 1) := by
    show (s₃.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [esp₃]
  refine ⟨⟨⟨hRv, fun i hi => ?_⟩, ⟨by rw [rd₃, wr₃, hea]; exact hin1, ?_, by rw [wr₃, hea]; exact hdw⟩⟩,
    b₃, esp₃, f₃', rd₃, wr₃⟩
  · have hpl : permOf d (R / 6) i < 8 * (R / 6) + 2 := dirPerm_lt (specDir d) hi
    have hl : permOf d (R / 6) i < Spec.Camellia.scheduleLength R := by
      simp only [Spec.Camellia.scheduleLength]; omega_using [hRv, hpl]
    rw [hws, schedWords_getD _ _ hl]
    exact e₃ i hi
  · rw [hea, f₃'.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hdw _ hs.wr).sub_right hsub
      · exact hsa.symm) (by decide)]
    exact hRa

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Camellia.Subkeys → Spec.Cbc.Cipher
  | .encrypt => Spec.Camellia.cipher
  | .decrypt => Spec.Camellia.invCipher

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
    Proof.Camellia.Prepared.Holds layout m (B.setWidth 64) R ws (specDir d) :=
  holds_of_words hfit hR (words_of_entries fun e he' => by
    rw [ofSpecDir_specDir, keyEntry_eq]; exact he e he')

theorem ready_of_holds {d : Dir} {m : Mem} {B : BitVec 32} {R : Nat} {ws : List (BitVec 64)}
    (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) (hR : R = 18 ∨ R = 24)
    (h : Proof.Camellia.Prepared.Holds layout m (B.setWidth 64) R ws (specDir d)) :
    ∀ i < 8 * (R / 6) + 2, EntryOk m B i (ws.getD (permOf d (R / 6) i) 0) := fun i hi => by
  have := entries_of_words (words_of_holds hfit hR h) hi
  rwa [ofSpecDir_specDir, keyEntry_eq] at this

/-- The table survives what keeps the bytes outside a batch's ranges. -/
theorem holds_of_keeps {R : Nat} {m m' : Mem} {B : BitVec 32} {w : List (BitVec 64)}
    {d : Spec.Camellia.Direction} (hR : R = 18 ∨ R = 24)
    (h : Proof.Camellia.Prepared.Holds layout m (B.setWidth 64) R w d)
    (hk : Proof.Camellia.Prepared.Keeps (B.setWidth 64) wsWords layout.cryptScratch m m') :
    Proof.Camellia.Prepared.Holds layout m' (B.setWidth 64) R w d := fun r hr i hi => by
  have hg : R / 6 ≤ 4 := by omega_using [hR]
  have hr' := hr
  rw [layout_table] at hr'
  simp only [List.mem_singleton] at hr'; subst hr'
  dsimp only at hi ⊢
  rw [hk (416 + i) (by simp only [wsWords, slots_eq]; omega_using [hR, hi]) (by
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [keySlot_eq, grpSlot_eq]; omega_using [hR, hi])]
  exact h _ hr i hi

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
  have hfB := hs.fit
  rw [dirCore_total] at hfB hst
  have hfit' : B.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_using [hfB]
  have hst' : Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨B.setWidth 64, 4 * slots⟩ :=
    hst.sub_right (Region.sub_prefix (by rw [slots_eq]; omega_using []))
  have hH := holds_of_ready hfit' hRv he
  show WP isa cryptCall s _
  refine WP.mono (cryptCall_wp hB (scrIn_of hs) hRv he ha.1 ha.2.1 hst' hesp)
    fun s' ⟨hB', cs, rd', wr', fS, hK, hbl⟩ => ?_
  have espS : s'.gpr .esp = s.gpr .esp := cs .esp (by decide)
  have hH' := holds_of_keeps hRv hH hK
  refine ⟨hB', espS, ⟨⟨hRv, ready_of_holds hfit' hRv hH'⟩, ⟨by rw [rd', wr', ea_arg espS, ← ea_arg (rfl)]; exact ha.1,
      ?_, by rw [wr', ea_arg espS, ← ea_arg rfl]; exact ha.2.2⟩⟩, fS, fun j hj => ?_, rd', wr'⟩
  · rw [ea_arg espS, ← ea_arg (s₀ := s) rfl]
    rw [fS.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact ha.2.1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (ha.2.2 _ hs.wr).sub_right (Region.sub_prefix (by simp only [dirCore_total]; rw [slots_eq]; omega_using []))
      · exact hsa.symm
  · have ha' : blkAddr (dirCore d) B j = B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot) + BitVec.ofNat 64 (16 * j) := rfl
    rw [dirCore_bw, show 4 * 4 = 16 from rfl, dirCipher_blockFn, bytesAt_eq_blockAt, ha', VG.Offset.add_add,
      hbl j hj]

/-- Camellia's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready s B k := (ReadyAt d s.mem B k ∧ RArg s k.1) ∧ B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32 ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨B.setWidth 64, 4 * (dirCore d).total⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨s.ea (argOp 1), 4⟩
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher, dirCore]
  layout := ⟨by simp only [dirCore]; decide, .inr rfl, by simp only [dirCore, slots_eq, tailSlot_eq]; omega_using [],
    by simp only [dirCore]; omega_using []⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame {_ _ _ k _} h e r w _ hf hs hd := by
    obtain ⟨⟨⟨hR, he⟩, ha⟩, hfit, hst, hsa⟩ := h
    have hg4 : 8 * (k.1 / 6) + 2 ≤ 34 := by omega_using [hR]
    exact ⟨⟨⟨hR, fun i hi => entry_keep hfit hf hd (by omega_using [hR, hi]) (he i hi)⟩, ha.frame e r w hf hs⟩, hfit,
      by rw [e]; exact hst, by rw [e, ea_arg e, ← ea_arg rfl]; exact hsa⟩
  prepare_wp {s _ _ _} hB hs hR hk hsp := WP.mono (prepare_wp d hB hs hR hk hsp) fun s' ⟨r, h⟩ => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hst, hsa, -⟩ := hk
    exact ⟨⟨r, hs.fit, by rw [h.2.1]; exact hst _ hR, by rw [h.2.1, ea_arg h.2.1, ← ea_arg rfl]; exact hsa⟩, h⟩
  crypt_wp hB hs hr hsp := WP.mono (crypt_wp d hB hs hr.1.1 hr.1.2 hr.2.2.1 hr.2.2.2 hsp)
    fun _ ⟨b, e, r, h⟩ => ⟨b, e, ⟨r, hr.2.1, by rw [e]; exact hr.2.2.1, by
      rw [e, ea_arg e, ← ea_arg rfl]; exact hr.2.2.2⟩, h⟩

end VG.Proof.Camellia.X86
