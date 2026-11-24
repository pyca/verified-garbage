module

import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Blowfish.FbScratch
import VerifiedGarbage.Proof.Modes.X86.Modes
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Proof.Modes.X86.Seq
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Blowfish.FbScratch
meta import VerifiedGarbage.Proof.Modes.X86.Modes
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Spec.Blowfish.Cfb
meta import VerifiedGarbage.Proof.Modes.X86.Seq
meta import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.Blowfish.X86.Modes
public import VerifiedGarbage.Proof.Blowfish.ModeBytes
public import VerifiedGarbage.Proof.Blowfish.X86.Ecb
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Blowfish.Schedule
meta import VerifiedGarbage.Proof.Modes.X86.Core
meta import VerifiedGarbage.Impl.Blowfish.X86.Modes
meta import VerifiedGarbage.Proof.Blowfish.ModeBytes
meta import VerifiedGarbage.Proof.Blowfish.X86.Ecb
meta import VerifiedGarbage.Proof.Blowfish.Blocks
meta import VerifiedGarbage.Proof.Blowfish.X86.Run
meta import VerifiedGarbage.Proof.Blowfish.Schedule

/-! ### `Blowfish.X86.ModeCore`, which only this module used -/

section

/-!
# Blowfish's core for the modes on x86 (32-bit)

`dirCoreSpec up`: Blowfish's core encrypting (`up`) or decrypting
(`Impl.Blowfish.X86.dirCore up`) meets what the modes need of a core
(`Proof.Modes.X86.CoreSpec`), with the key the schedule at the address in the
first stack argument, read in place, its cipher `Spec.Blowfish.cipher` or
`Spec.Blowfish.invCipher` under it, and the key ready whenever that schedule
and its address are still there, apart from every writable region (`Ready`):
`prepare` does nothing.

`Fits cs w n`: what the lemmas about the functions need of a core and its
`CoreSpec` (its key a schedule through the first stack argument, blocks of
two words, `n` bytes of stack, a scratch buffer of `w` 64-bit words), which
this core has with 11 words and no stack (`dirFits`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)

/-! ## The key -/

/-- The schedule `k` at `S`, the address in the first stack argument; both
readable, the schedule not wrapping around. -/
def SchedAt (s : State) (k : Schedule) (S : BitVec 32) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (at_ .esp 4)) 4 ∧ s.mem.readW (s.ea (at_ .esp 4)) 32 = S ∧
    k = scheduleAt s.mem (S.setWidth 64) ∧ (⟨S.setWidth 64, 4168⟩ : Region) ∈ s.rd ++ s.wr ∧
    S.toNat + 4168 ≤ 2 ^ 32

/-- The schedule at `S` and the argument at `a` are apart from the regions `rs`. -/
def Apart (S : BitVec 32) (a : Addr) (rs : List Region) : Prop :=
  ∀ r ∈ rs, Region.Disjoint ⟨S.setWidth 64, 4168⟩ r ∧ Region.Disjoint ⟨a, 4⟩ r

/-- The schedule through the first stack argument, apart from the regions `rs`
and from every writable region. -/
def KeyArgs (s : State) (rs : List Region) (k : Schedule) : Prop :=
  ∃ S, SchedAt s k S ∧ Apart S (s.ea (at_ .esp 4)) rs ∧ Apart S (s.ea (at_ .esp 4)) s.wr

/-- The schedule through the first stack argument, apart from every writable
region. -/
def Ready (s : State) (k : Schedule) : Prop :=
  ∃ S, SchedAt s k S ∧ Apart S (s.ea (at_ .esp 4)) s.wr

theorem Apart.sub {S : BitVec 32} {a : Addr} {ws rs : List Region} (h : Apart S a ws)
    (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') : Apart S a rs := fun r hr => by
  obtain ⟨r', hr', hsub⟩ := hs r hr
  exact ⟨(h r' hr').1.sub_right hsub, (h r' hr').2.sub_right hsub⟩

theorem SchedAt.frame {s s' : State} {k : Schedule} {S : BitVec 32} {rs : List Region} (h : SchedAt s k S)
    (ha : Apart S (s.ea (at_ .esp 4)) rs) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) : SchedAt s' k S := by
  obtain ⟨hin, hv, hk, hsch, hfit⟩ := h
  obtain hea : s'.ea (at_ .esp 4) = s.ea (at_ .esp 4) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨by rw [hrd, hwr, hea]; exact hin, ?_, ?_, by rw [hrd, hwr]; exact hsch, hfit⟩
  · rw [hea, hf.readW (Region.contains_self _ _) (fun r hr => (ha r hr).2) (by decide), hv]
  · rw [hk, scheduleAt_eq_of_frame _ hf fun r hr => (ha r hr).1]

theorem Ready.frame {s s' : State} {k : Schedule} {rs : List Region} (h : Ready s k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r') : Ready s' k := by
  obtain ⟨S, hS, ha⟩ := h
  obtain hea : s'.ea (at_ .esp 4) = s.ea (at_ .esp 4) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  exact ⟨S, hS.frame (ha.sub hs) hesp hrd hwr hf, by rw [hwr, hea]; exact ha⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨S, hS, ha, hw⟩ := h
  obtain hea : s'.ea (at_ .esp 4) = s.ea (at_ .esp 4) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  exact ⟨S, hS.frame ha hesp hrd hwr hf, by rw [hea]; exact ha, by rw [hwr, hea]; exact hw⟩

/-! ## The block -/

theorem addr_slot48 {B : BitVec 32} (h : B.toNat + 48 ≤ 2 ^ 32) {d : Nat} (hd : d < 48) :
    addr B d = slot B d := addr_of_fit (by omega_using [h, hd])

/-- `ebp` the scratch buffer, and the buffer's address to the data pointer. -/
theorem setup_run (u : State) {B : BitVec 32} (hb : u.gpr .edi = B) (bfit : B.toNat + 48 ≤ 2 ^ 32)
    (w32 : InRegions u.wr (slot B 32) 4) :
    WP isa (.block modeSetup) u fun t =>
      t.mem = u.mem.writeW (slot B 32) (B + BitVec.ofNat 32 40) ∧ t.gpr .ebp = B := by
  unfold modeSetup
  brun [bufOff, hb, addr_slot48 bfit, w32]

/-- The halves to the buffer through `ebp`, and `edi` the scratch buffer. -/
theorem store_run (u : State) {B : BitVec 32} (hb : u.gpr .ebp = B) (bfit : B.toNat + 48 ≤ 2 ^ 32)
    (r16 : InRegions (u.rd ++ u.wr) (slot B 16) 4) (r20 : InRegions (u.rd ++ u.wr) (slot B 20) 4)
    (w40 : InRegions u.wr (slot B 40) 4) (w44 : InRegions u.wr (slot B 44) 4) :
    WP isa (.block modeStore) u fun t =>
      t.mem = (u.mem.writeW (slot B 40) (bswap (u.mem.readW (slot B 16) 32))).writeW (slot B 44)
        (bswap (u.mem.readW (slot B 20) 32)) ∧ t.gpr .edi = B := by
  obtain e : ∀ v : BitVec 32, (u.mem.writeW (slot B 40) v).readW (slot B 20) 32 = u.mem.readW (slot B 20) 32 :=
    fun v => Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  unfold modeStore
  brun [bufOff, hb, addr_slot48 bfit, r16, r20, w40, w44, e]

/-- The block stored as two big-endian words. -/
theorem stored_block (m : Mem) (Pa : Addr) (L R : BitVec 32) :
    blockAt ((m.writeW Pa (bswap L)).writeW (Pa + BitVec.ofNat 64 4) (bswap R)) Pa = encodeBlock L R := by
  refine blockAt_eq _ _ _ fun i hi => ?_
  rw [encodeBlock_getD _ _ hi]
  by_cases h4 : i < 4
  · rw [ite_eq_left h4, writeW32_other _ (Offset.disjoint Pa (d := i) (n := 1) (e := 4) (k := 4) (by omega_using [h4])
      (by omega_using [hi]) (by decide)), st_byte _ _ _ h4, bswap_byte _ h4]
  · rw [ite_eq_right h4, show i = 4 + (i - 4) by omega_using [h4], ← Offset.add_add, st_byte _ _ _ (by omega_using [hi]),
      bswap_byte _ (by omega_using [hi])]
    congr 2; omega_using []

theorem dirCore_total (up : Bool) : (dirCore up).total = 22 := rfl
theorem dirCore_ka (up : Bool) : (dirCore up).ka = 1 := rfl

theorem crypt_wp (up : Bool) {s : State} {B : BitVec 32} {k : Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore up).total)
    (hr : Ready s k) :
    WP isa (dirCore up).crypt s fun s' => s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Ready s' k ∧ Frame [coreRegion (dirCore up) B, stkRegion (s.gpr .esp) (dirCore up).stack] s.mem s'.mem ∧
      (∀ j < (dirCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw) =
        dirCipher up k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨S, ⟨hin, hv, hk, hsch, hSfit⟩, ha⟩ := hr
  have hB' : s.gpr .edi = B := hB
  have hfit := hs.fit
  rw [dirCore_total] at hfit
  obtain bfit : B.toNat + 48 ≤ 2 ^ 32 := by omega_using [hfit]
  have scr : (⟨B.setWidth 64, 88⟩ : Region) ∈ s.wr := hs.wr
  have hea : s.ea (at_ .esp 4) = addr (s.gpr .esp) 4 := rfl
  obtain wS : ∀ d, d + 4 ≤ 48 → InRegions s.wr (slot B d) 4 := fun d hd =>
    ⟨_, scr, Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩
  obtain core48 : Region.Sub ⟨B.setWidth 64, 48⟩ ⟨B.setWidth 64, 88⟩ := Region.sub_prefix (by decide)
  obtain aS := (ha _ scr).1
  obtain aA := (ha _ scr).2
  let Pa := slot B 40
  obtain e44 : Pa + BitVec.ofNat 64 4 = slot B 44 := Offset.add_add _ _ _
  show WP isa (.seq (.block (modeSetup ++ loadBlock)) (.seq (cipher 4 up) (.block modeStore))) s _
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.ebp, .ebx] (setup_run s hB' bfit (wS 32 (by decide))) (by decide))
    fun u₁ ⟨⟨m₁, bp₁⟩, k₁⟩ => ?_
  have wr₁ : u₁.wr = s.wr := k₁.2.2
  have rd₁ : u₁.rd = s.rd := k₁.2.1
  obtain w₁ : ∀ d, d + 4 ≤ 48 → InRegions u₁.wr (slot B d) 4 := fun d hd => by rw [wr₁]; exact wS d hd
  obtain e0 : addr (B + BitVec.ofNat 32 40) 0 = Pa := by
    unfold addr; rw [ofs_add, ← addr, addr_slot48 bfit (by decide)]
  obtain e4 : addr (B + BitVec.ofNat 32 40) 4 = Pa + BitVec.ofNat 64 4 := by
    unfold addr; rw [ofs_add, ← addr, addr_slot48 bfit (by decide), e44]
  refine WP.mono (WP.keep [.eax, .ebx] (loadBlock_run u₁ (B := B) bp₁ (by omega_using [hfit]) (w₁ 16 (by decide))
    (w₁ 20 (by decide)) (region_in (w₁ 32 (by decide)))
    (by rw [m₁, Mem.readW_writeW_self32]) e0 e4 (region_in (w₁ 40 (by decide)))
    (by rw [e44]; exact region_in (w₁ 44 (by decide)))
    (by rw [e44]; exact Offset.sep _ (by decide) (by decide) (by decide))) (by decide))
    fun u₂ ⟨m₂, k₂⟩ => ?_
  obtain k₁₂ : Keep [.ebp, .ebx, .eax] s u₂ := (k₁.trans k₂).mono (by decide)
  obtain esp₂ : u₂.gpr .esp = s.gpr .esp := k₁₂.gpr (by decide)
  obtain F₂ : Frame [⟨B.setWidth 64, 48⟩] s.mem u₂.mem := by
    rw [m₂, m₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 32) (n := 4)
      (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 16) (n := 4)
      (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 20) (n := 4)
      (by decide) (by decide))
  obtain wide : ∀ {m m' : Mem}, Frame [⟨B.setWidth 64, 48⟩] m m' → Frame [⟨B.setWidth 64, 88⟩] m m' := fun hf =>
    hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, core48⟩
  obtain apS : Apart S (s.ea (at_ .esp 4)) [⟨B.setWidth 64, 88⟩] := ha.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, scr, fun _ h => h⟩
  -- the block in, as the halves
  obtain blk₁ : blockAt u₁.mem Pa = blockAt s.mem Pa := by
    rw [m₁]
    exact blockAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by decide) (by decide) (by decide)
  -- the cipher
  obtain CE : CipherEnv 4 S B u₂ := by
    refine ⟨(k₂.gpr (by decide)).trans bp₁, by omega_using [hfit], ?_, ?_, ?_, hSfit, fun o ho => ?_, ?_, ?_⟩
    · rw [k₂.2.2, wr₁]; exact ⟨_, scr, contains_pre _ (by decide)⟩
    · rw [keep_reads k₁₂, esp₂, ← hea]; exact hin
    · rw [esp₂, ← hea, (wide F₂).readW (Region.contains_self _ _) (fun r hr => (apS r hr).2) (by decide)]; exact hv
    · rw [keep_reads k₁₂]; exact ⟨_, hsch, Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])⟩
    · exact aS.symm.sub_left (Region.sub_prefix (by decide))
    · rw [esp₂, ← hea]; exact aA.symm.sub_left (Region.sub_prefix (by decide))
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun u₃ ⟨c₃, ck₃, cf₃⟩ => ?_
  obtain k₃ : Keep [.ebp, .ebx, .eax, .ecx, .edx, .esi, .edi] s u₃ := (k₁₂.trans ck₃).mono (by decide)
  obtain F₃ : Frame [⟨B.setWidth 64, 48⟩] s.mem u₃.mem :=
    F₂.trans (cf₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)
  obtain w₃ : ∀ d, d + 4 ≤ 48 → InRegions u₃.wr (slot B d) 4 := fun d hd => by rw [k₃.2.2]; exact wS d hd
  -- the block out
  refine WP.mono (WP.keep [.eax, .edi] (store_run u₃ ((ck₃.gpr (by decide)).trans CE.bp) bfit
    (region_in (w₃ 16 (by decide))) (region_in (w₃ 20 (by decide))) (w₃ 40 (by decide)) (w₃ 44 (by decide))) (by
      decide))
    fun u₄ ⟨⟨m₄, di₄⟩, k₄⟩ => ?_
  obtain k₄' : Keep [.ebp, .ebx, .eax, .ecx, .edx, .esi, .edi] s u₄ := (k₃.trans k₄).mono (by decide)
  obtain esp₄ : u₄.gpr .esp = s.gpr .esp := k₄'.gpr (by decide)
  obtain F₄ : Frame [⟨B.setWidth 64, 48⟩] s.mem u₄.mem := by
    rw [m₄]
    exact (F₃.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 40) (n := 4) (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 44) (n := 4) (by decide)
      (by decide))
  have rd₄ : u₄.rd = s.rd := k₄'.2.1
  have wr₄ : u₄.wr = s.wr := k₄'.2.2
  obtain hS : SchedAt s k S := ⟨hin, hv, hk, hsch, hSfit⟩
  refine ⟨di₄, esp₄, ⟨S, hS.frame apS esp₄ rd₄ wr₄ (wide F₄),
      by rw [wr₄, show u₄.ea (at_ .esp 4) = s.ea (at_ .esp 4) by
        show (u₄.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [esp₄]]; exact ha⟩,
    F₄.sub fun r hr => ?_, fun j hj => ?_, rd₄, wr₄⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · obtain rfl : j = 0 := by simp only [dirCore] at hj; omega_using [hj]
    obtain hba : blkAddr (dirCore up) B 0 = Pa := by
      simp only [blkAddr, slotA, dirCore, Offset.add_add]; rfl
    obtain e16 : u₂.mem.readW (slot B 16) 32 = decodeWord (blockAt u₁.mem Pa) 0 := by
      rw [m₂, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32]
    obtain e20 : u₂.mem.readW (slot B 20) 32 = decodeWord (blockAt u₁.mem Pa) 4 := by
      rw [m₂, Mem.readW_writeW_self32]
    rw [e16, e20, blk₁] at c₃
    obtain hK : scheduleAt u₂.mem (S.setWidth 64) = k := by
      rw [hk]; exact scheduleAt_eq_of_frame _ (wide F₂) fun r hr => (apS r hr).1
    rw [hK] at c₃
    rw [hba]
    simp only [dirCore, Nat.reduceMul]
    rw [dirCipher_bytes, bytesAt_eq, m₄, ← e44, stored_block, show dirBlock k up = blockOut k up from rfl,
      blockOut_eq, ← c₃]

/-- Blowfish's core encrypting (`up`) or decrypting meets what the modes need. -/
def dirCoreSpec (up : Bool) : CoreSpec (dirCore up) where
  Key := Schedule
  cipher := dirCipher up
  KeyArgs := KeyArgs
  Ready s B k := Ready s k ∧ B.toNat + 4 * (dirCore up).total ≤ 2 ^ 32
  cipher_len _ _ := dirCipher_len _ _ _
  layout := ⟨by simp only [dirCore]; decide, .inl rfl, by simp only [dirCore]; omega_using [],
    by simp only [dirCore]; omega_using []⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h e r w _ hf hs _ := ⟨h.1.frame e r w hf hs, h.2⟩
  prepare_wp hB hs _ hk _ := by
    obtain ⟨S, hS, -, hw⟩ := hk
    refine WP.block_nil ⟨⟨⟨S, hS, hw⟩, hs.fit⟩, hB, rfl, Frame.refl _ _, rfl, rfl⟩
  crypt_wp hB hs hr _ := WP.mono (crypt_wp up hB hs hr.1) fun _ ⟨b, e, r, h⟩ => ⟨b, e, ⟨r, hr.2⟩, h⟩

/-! ## Cores that fit the functions -/

/-- What the functions give a core with `n` bytes of stack of the key:
`KeyArgs`, and the stack apart from the regions `rs`, from the schedule and
from the argument that holds its address. -/
def KeyArgsN (n : Nat) (s : State) (rs : List Region) (k : Schedule) : Prop :=
  KeyArgs s rs k ∧ (∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .esp) n) r) ∧
    Region.Disjoint (stkRegion (s.gpr .esp) n) ⟨(arg s 0).setWidth 64, 4168⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) n) ⟨s.ea (at_ .esp 4), 4⟩

/-- A core of Blowfish's modes on x86 with its `CoreSpec`, as the lemmas
about the functions take it (`scr_eq`, `Fb.seqPre_of`, `Fb.keyArgs_of` and
the functions' `_of` theorems): its key is a schedule, read through the
first stack argument (`KeyArgsN`); its blocks are two words; the key is one
argument; it has `n` bytes of stack; and its scratch buffer is `w` 64-bit
words. -/
structure Fits {c : VG.Impl.Modes.X86.Core} (cs : CoreSpec c) (w n : Nat) where
  toKey : Schedule → cs.Key
  keyArgs : ∀ {s : State} {rs : List Region} {k : Schedule}, KeyArgsN n s rs k → cs.KeyArgs s rs (toKey k)
  bw : c.bw = 2
  ka : c.ka = 1
  stack : c.stack = n
  total : c.total = 2 * w

/-- The core a block at a time fits, with 11 words and no stack. -/
def dirFits (up : Bool) : Fits (dirCoreSpec up) 11 0 := ⟨id, fun h => h.1, rfl, rfl, rfl, rfl⟩

end VG.Proof.Blowfish.X86

end

end

/-!
# Blowfish-OFB and Blowfish-CFB64 on x86 (32-bit) meet their contracts

`ofb_wp_of`, `cfbEncrypt_wp_of`, `cfbDecrypt_wp_of`: the modes' OFB and CFB
(`Proof.Modes.X86.ofb_wp`, `cfbEnc_wp`, `cfbDec_wp`) over any core that fits
(`Fits cs w n`) whose cipher is Blowfish's, with the working space, `w`
64-bit words, as a fifth argument and `n` bytes of stack below `esp`
(`fbX86 w n`); `ofb_wp_x86`, `cfbEncrypt_wp`, `cfbDecrypt_wp` are those of
Blowfish's core (`dirCoreSpec true`, 11 words, no stack). The contract's
narrowing (`fb_verified`) and the initial taint (`fbTaint w n`) are for any
`w` and `n`. The chaining value is written back, so it is
writable, and the taint analysis knows the argument words holding the
addresses of the data, the chaining value and the scratch buffer as the base
addresses of the writable regions. The `_framed` theorems run them with
their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish.X86

theorem disjoint_empty (r : Region) (a : Addr) : Region.Disjoint ⟨a, 0⟩ r := fun _ h => by
  simp only [Region.Contains] at h; omega_arith

/-- No byte below the stack pointer: apart from every region. -/
theorem below0 (e : BitVec 32) (r : Region) : Region.Disjoint (below e 0) r := disjoint_empty _ _

/-- The scratch buffer of a core that fits is the fifth argument's `w` words. -/
theorem scr_eq {c : VG.Impl.Modes.X86.Core} {cs : Proof.Modes.X86.CoreSpec c} {w n : Nat} (f : Fits cs w n)
    (s : State) : Modes.X86.scrR s c = ⟨(arg s 4).setWidth 64, 8 * w⟩ := by
  show (⟨(arg s (c.ka + 3)).setWidth 64, 4 * c.total⟩ : Region) = _
  rw [f.ka, f.total, show 4 * (2 * w) = 8 * w by omega_arith]

/-- The `n` bytes of stack below `esp` are apart from the arguments and the return address. -/
theorem stk_apart {s : State} {n : Nat} (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) (hlo : n ≤ (s.gpr .esp).toNat) :
    Region.Disjoint (Proof.Modes.X86.stkRegion (s.gpr .esp) n) ⟨argAddr s 0, 20⟩ ∧
      Region.Disjoint (Proof.Modes.X86.stkRegion (s.gpr .esp) n) ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  have e : (s.gpr .esp - BitVec.ofNat 32 n).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 n :=
    VG.X86.Taint.sub_setWidth hlo
  have ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_arith)
  refine ⟨?_, ?_⟩
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 n).setWidth 64, n⟩ _
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by omega_arith)
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 n).setWidth 64, n⟩ _
    have := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := n) (a := 0) (l := 4) (by omega_arith)
    rw [BitVec.add_zero] at this
    rw [e]; exact this

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_chunks (m : Mem) (p : Addr) (n : Nat) :
    Spec.Blowfish.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n := by
  simp only [Spec.Blowfish.cbcBlocksAt, Spec.Blowfish.blocksAt, Proof.Modes.chunksAt, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

end VG.Proof.Blowfish.X86

namespace VG.Proof.Blowfish.X86.Fb

open VG VG.X86 VG.Impl.Blowfish.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre ofb_wp cfbEnc_wp cfbDec_wp)
open VG.Proof.Modes.X86 (stkRegion)
open VG.Proof.Blowfish.X86 (scr_eq disjoint_empty KeyArgs KeyArgsN Fits dirFits stk_apart below0 dirCoreSpec
  cbcBlocksAt_chunks)

/-- Blowfish under the schedule at the first argument. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Blowfish.cipher (Spec.Blowfish.scheduleAt s.mem ((arg s 0).setWidth 64))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m ((arg s 1).setWidth 64) 8
/-- The data. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Blowfish.cbcBlocksAt m ((arg s 2).setWidth 64) (arg s 3).toNat

/-- The functions' postconditions. -/
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (arg s 3).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- OFB or CFB64 on x86 with its working space, `w` 64-bit words, as the
fifth argument, `n` bytes of stack below `esp`, and the postcondition
`post`. -/
def fbX86 (w n : Nat) (post : State → State → Prop) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 4168⟩
    let iv : Region := ⟨(arg s 1).setWidth 64, 8⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * w⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) n
    s.rd = [sched, args] ∧ s.wr = [data, iv, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint iv ∧ sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
    stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint iv ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 4168 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * w ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ n ≤ (s.gpr .esp).toNat
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `fbX86`'s precondition gives the modes', for a core that fits. -/
theorem seqPre_of {c : VG.Impl.Modes.X86.Core} {cs : Proof.Modes.X86.CoreSpec c} {w n : Nat} (f : Fits cs w n)
    {post : State → State → Prop} {M : Mode} (hstep : M.step = 8) {s : State} (h : (fbX86 w n post).pre s) :
    SeqPre c M s := by
  obtain ⟨hrd, hwr, dKD, dKV, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, dSK, dSD, dSV, dSS, fK, fV, fD, fS,
    fE, fLo⟩ := h
  have hL := cs.layout
  obtain ⟨sA, sR⟩ := stk_apart fE fLo
  obtain hka := f.ka
  obtain hbw := f.bw
  obtain hsk := f.stack
  obtain htot := f.total
  obtain hroom := hL.room
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => ?_), ?_, ?_, ?_, ?_, ?_, ?_, hL⟩
  · show (⟨argAddr s 0, 4 * (c.ka + 4)⟩ : Region) ∈ _
    rw [hrd, hka]; simp
  · rw [hka]; exact fE
  · show (⟨(arg s (c.ka + 3)).setWidth 64, 4 * c.total⟩ : Region) ∈ _
    rw [hwr, hka, htot, show 4 * (2 * w) = 8 * w by omega_arith]; simp
  · show (arg s (c.ka + 3)).toNat + 4 * c.total ≤ 2 ^ 32
    rw [hka, htot]
    show (arg s 4).toNat + 4 * (2 * w) ≤ 2 ^ 32
    omega_arith
  · show (⟨(arg s c.ka).setWidth 64, 4 * c.bw⟩ : Region) ∈ _
    rw [hwr, hka, hbw]; simp
  · show (⟨(arg s c.ka).setWidth 64, 4 * c.bw⟩ : Region) ∈ _
    rw [hwr, hka, hbw]; simp
  · show (arg s c.ka).toNat + 4 * c.bw ≤ 2 ^ 32
    rw [hka, hbw]; omega_arith
  · show Proof.Modes.X86.dataRegion (arg s (c.ka + 1)) M.step (arg s (c.ka + 2)).toNat ∈ _
    rw [hwr, hstep, hka]; simp [Proof.Modes.X86.dataRegion]
  · show (arg s (c.ka + 1)).toNat + M.step * (arg s (c.ka + 2)).toNat ≤ 2 ^ 32
    rw [hstep, hka]; exact fD
  · show Region.Disjoint (Proof.Modes.X86.dataRegion (arg s (c.ka + 1)) M.step (arg s (c.ka + 2)).toNat) _
    rw [hstep, scr_eq f, hka]; exact dDS
  · show Region.Disjoint ⟨(arg s c.ka).setWidth 64, 4 * c.bw⟩ _
    rw [scr_eq f, hka, hbw]; exact dVS
  · show Region.Disjoint ⟨(arg s c.ka).setWidth 64, 4 * c.bw⟩
      (Proof.Modes.X86.dataRegion (arg s (c.ka + 1)) M.step (arg s (c.ka + 2)).toNat)
    rw [hstep, hka, hbw]; exact dVD
  · show Region.Disjoint ⟨argAddr s 0, 4 * (c.ka + 4)⟩ _
    rw [scr_eq f, hka]; exact dAS
  · show Region.Disjoint ⟨argAddr s 0, 4 * (c.ka + 4)⟩
      (Proof.Modes.X86.dataRegion (arg s (c.ka + 1)) M.step (arg s (c.ka + 2)).toNat)
    rw [hstep, hka]; exact dAD
  · rw [scr_eq f]; exact dRS
  · show Region.Disjoint _ (Proof.Modes.X86.dataRegion (arg s (c.ka + 1)) M.step (arg s (c.ka + 2)).toNat)
    rw [hstep, hka]; exact dRD
  · show Region.Disjoint _ ⟨(arg s c.ka).setWidth 64, 4 * c.bw⟩
    rw [hka, hbw]; exact dRV
  · show Region.Disjoint (stkRegion (s.gpr .esp) c.stack)
      (Proof.Modes.X86.dataRegion (arg s (c.ka + 1)) M.step (arg s (c.ka + 2)).toNat)
    rw [hstep, hka, hsk]; exact dSD
  · show Region.Disjoint (stkRegion (s.gpr .esp) c.stack) ⟨Proof.Modes.X86.slotA (arg s (c.ka + 3)) c.slots, 40⟩
    rw [hka, hsk]
    exact dSS.sub_right (VG.Offset.sub_base _ (by omega_arith))
  · show Region.Disjoint (stkRegion (s.gpr .esp) c.stack) ⟨argAddr s 0, 4 * (c.ka + 4)⟩
    rw [hka, hsk]; exact sA
  · rw [hsk]; exact sR
  · rw [hsk]; exact fLo
  · rw [hstep, hbw]; exact ⟨by decide, by decide⟩

/-- `fbX86`'s precondition gives the key's, for a core that fits. -/
theorem keyArgs_of {c : VG.Impl.Modes.X86.Core} {cs : Proof.Modes.X86.CoreSpec c} {w n : Nat} (f : Fits cs w n)
    {post : State → State → Prop} {s : State} (h : (fbX86 w n post).pre s) :
    cs.KeyArgs s [Modes.X86.scrR s c] (f.toKey (Spec.Blowfish.scheduleAt s.mem ((arg s 0).setWidth 64))) := by
  obtain ⟨hrd, hwr, dKD, dKV, dKS, -, -, -, dAD, dAV, dAS, -, -, -, dSK, -, -, dSS, fK, -, -, -, fE, fLo⟩ := h
  have hA : ∀ r : Region, (⟨argAddr s 0, 20⟩ : Region).Disjoint r → Region.Disjoint ⟨s.ea (at_ .esp 4), 4⟩ r :=
    fun r h => h.sub_left (Region.sub_prefix (by decide))
  refine f.keyArgs ⟨⟨arg s 0, ⟨⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK⟩,
    fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_, dSK,
    (stk_apart fE fLo).1.sub_right (Region.sub_prefix (by decide))⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq f]; exact ⟨dKS, hA _ dAS⟩
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [⟨dKD, hA _ dAD⟩, ⟨dKV, hA _ dAV⟩, ⟨dKS, hA _ dAS⟩]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq f]; exact dSS

/-- The data and the chaining value of the modes' results, as the postconditions have them. -/
theorem data_eq (m : Mem) (s : State) :
    Proof.Modes.chunksAt 8 m ((arg s 2).setWidth 64) (arg s 3).toNat = dataAt m s :=
  (cbcBlocksAt_chunks _ _ _).symm
theorem iv_eq (m : Mem) (s : State) : Spec.Aes.bytesAt m ((arg s 1).setWidth 64) 8 = ivAt m s := rfl

/-- The modes' results (`h`, `h'`) for the core that fits by `f`, whose
cipher `hc` gives, as the functions' postconditions state them. -/
tactic_template "bf_post_eq " f:term:max hc:term:max h:ident h':ident : tactic =>
  `(tactic| simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
                     Proof.Modes.X86.N, VG.Proof.Blowfish.X86.Fits.ka $f, VG.Proof.Blowfish.X86.Fits.bw $f,
                     Nat.reduceAdd, Nat.reduceMul, VG.Proof.Blowfish.X86.Fb.data_eq, VG.Proof.Blowfish.X86.Fb.iv_eq,
                     $hc:term] at $h:ident $h':ident)

section
variable {c : VG.Impl.Modes.X86.Core} {cs : Proof.Modes.X86.CoreSpec c} {w n : Nat}

/-- A whole block is a step of the modes over a core that fits. -/
theorem step_block (f : Fits cs w n) : 4 * c.bw = 8 := by rw [f.bw]

/-- OFB over any core that fits, whose cipher is Blowfish's. -/
theorem ofb_wp_of (f : Fits cs w n) (hc : ∀ k, cs.cipher (f.toKey k) = Spec.Blowfish.cipher k) {s₀ : State}
    (hp : (fbX86 w n ofbPost).pre s₀) :
    WP isa (c.seq (Mode.ofb c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 w n ofbPost).post s₀ s' :=
  WP.mono (ofb_wp cs (seqPre_of f (step_block f) hp) (keyArgs_of f hp))
    fun _ ⟨h1, h2, h3⟩ => by bf_post_eq f hc h2 h3; exact ⟨h1, h2, h3⟩

/-- CFB64 encryption over any core that fits. -/
theorem cfbEncrypt_wp_of (f : Fits cs w n) (hc : ∀ k, cs.cipher (f.toKey k) = Spec.Blowfish.cipher k) {s₀ : State}
    (hp : (fbX86 w n cfbEncPost).pre s₀) :
    WP isa (c.seq (Mode.cfbEnc c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 w n cfbEncPost).post s₀ s' :=
  WP.mono (cfbEnc_wp cs (seqPre_of f (step_block f) hp) (keyArgs_of f hp))
    fun _ ⟨h1, h2, h3⟩ => by bf_post_eq f hc h2 h3; exact ⟨h1, h2, h3⟩

/-- CFB64 decryption over any core that fits. -/
theorem cfbDecrypt_wp_of (f : Fits cs w n) (hc : ∀ k, cs.cipher (f.toKey k) = Spec.Blowfish.cipher k) {s₀ : State}
    (hp : (fbX86 w n cfbDecPost).pre s₀) :
    WP isa (c.seq (Mode.cfbDec c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 w n cfbDecPost).post s₀ s' :=
  WP.mono (cfbDec_wp cs (seqPre_of f (step_block f) hp) (keyArgs_of f hp))
    fun _ ⟨h1, h2, h3⟩ => by bf_post_eq f hc h2 h3; exact ⟨h1, h2, h3⟩

end

theorem ofb_wp_x86 {s₀ : State} (hp : (fbX86 11 0 ofbPost).pre s₀) :
    WP isa ofb s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 11 0 ofbPost).post s₀ s' :=
  ofb_wp_of (dirFits true) (fun _ => rfl) hp

theorem cfbEncrypt_wp {s₀ : State} (hp : (fbX86 11 0 cfbEncPost).pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 11 0 cfbEncPost).post s₀ s' :=
  cfbEncrypt_wp_of (dirFits true) (fun _ => rfl) hp

theorem cfbDecrypt_wp {s₀ : State} (hp : (fbX86 11 0 cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 11 0 cfbDecPost).post s₀ s' :=
  cfbDecrypt_wp_of (dirFits true) (fun _ => rfl) hp

/-! ## Constant time -/

/-- The initial taint: `esp` public, and the words holding `data`, `iv` and
`scratch` known to be the base addresses of the writable regions. -/
def fbTaint (w n : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8, 8 * w], argLen := 24,
    argBases := [(12, 0), (8, 1), (20, 2)], room := n }

theorem fbTaint_wf {w n : Nat} {post : State → State → Prop} {s : State} (hp : (fbX86 w n post).pre s) :
    VG.X86.Taint.Wf (fbTaint w n) s := by
  obtain ⟨hrd, hwr, dKD, dKV, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, dSK, dSD, dSV, dSS, fK, fV, fD, fS,
    fE, fLo⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [fbTaint]; omega_arith, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨dVD.symm, dDS⟩, dVS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRV dAV
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRS dAS
  · intro p hp'
    simp only [fbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by show _ + 4 ≤ 24; decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨fLo, fun r hr => ?_⟩
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 n = (s.gpr .esp - BitVec.ofNat 32 n).setWidth 64 :=
      (VG.X86.Taint.sub_setWidth fLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 n, n⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [dSD, dSV, dSS]

theorem fbTaint_agree {w n : Nat} {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (fbX86 w n post).pre s₁)
    (h₂ : (fbX86 w n post).pre s₂) (hpub : (fbX86 w n post).pub s₁ s₂) :
    VG.X86.Taint.Agree (fbTaint w n) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, fbTaint_wf h₁, fbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 1 (by omega_arith), ha 2 (by omega_arith), ha 3 (by omega_arith), ha 4 (by omega_arith)]
  · simp only [fbTaint] at hk
    rw [show VG.X86.Taint.depth (fbTaint w n).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 24) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg _ (ha _ (by omega_arith))

theorem ofb_ct : ConstantTime isa (fbX86 11 0 ofbPost).pre (fbX86 11 0 ofbPost).pub ofb :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 11 0) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbEncrypt_ct : ConstantTime isa (fbX86 11 0 cfbEncPost).pre (fbX86 11 0 cfbEncPost).pub cfbEncrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 11 0) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa (fbX86 11 0 cfbDecPost).pre (fbX86 11 0 cfbDecPost).pub cfbDecrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 11 0) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

/-- `fbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`fb_verified` narrows to `fbX86`). -/
def wideContract (w n : Nat) (post : State → State → Prop) : Contract isa :=
  { fbX86 w n post with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 4168⟩
      let iv : Region := ⟨(arg s 1).setWidth 64, 8⟩
      let data : Region := ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * w⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) n
      s.rd = [sched] ∧ s.wr = [iv, data, scratch, args] ∧
      sched.Disjoint data ∧ sched.Disjoint iv ∧ sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint iv ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 4168 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * w ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ n ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 4168⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (w : Nat) (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩, ⟨(arg s 1).setWidth 64, 8⟩, ⟨(arg s 4).setWidth 64, 8 * w⟩]

tactic_template "narrow_blowfish_x86_fbverified" : tactic => `(tactic| simp only [VG.Proof.Blowfish.X86.Fb.fbX86, VG.Proof.Blowfish.X86.Fb.wideContract,
                     VG.Proof.Blowfish.X86.Fb.narrowRd, VG.Proof.Blowfish.X86.Fb.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])
tactic_template "narrow_blowfish_x86_fbverified" loc:Lean.Parser.Tactic.location : tactic => `(tactic| simp only [VG.Proof.Blowfish.X86.Fb.fbX86, VG.Proof.Blowfish.X86.Fb.wideContract,
                     VG.Proof.Blowfish.X86.Fb.narrowRd, VG.Proof.Blowfish.X86.Fb.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)

theorem wide_pre (w n : Nat) (post : State → State → Prop) (s : State) (h : (wideContract w n post).pre s) :
    (fbX86 w n post).pre (s.withRegions (narrowRd s) (narrowWr w s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow_blowfish_x86_fbverified
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x50 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x5000, 4168⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 88⟩, ⟨0x8004, 20⟩]

theorem wide_implies_ofb :
    (wideContract 11 0 ofbPost).Implies (Proof.Blowfish.fbScratchContract X86.abi 11 Proof.Blowfish.ofbPost) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost] at h
    sig_split h
    sig_reduce [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | with_reducible exact below0 _ _
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost]
  · sig_implies_sat [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbEnc :
    (wideContract 11 0 cfbEncPost).Implies (Proof.Blowfish.fbScratchContract X86.abi 11 Proof.Blowfish.cfbEncPost) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost] at h
    sig_split h
    sig_reduce [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | with_reducible exact below0 _ _
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost]
  · sig_implies_sat [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbDec :
    (wideContract 11 0 cfbDecPost).Implies (Proof.Blowfish.fbScratchContract X86.abi 11 Proof.Blowfish.cfbDecPost) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost] at h
    sig_split h
    sig_reduce [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | with_reducible exact below0 _ _
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
  · sig_implies_sat [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

/-- A state satisfying the functions' precondition: the schedule at `0x1000`,
the chaining value at `0x2000`, and no blocks at `0x3000`, as stack arguments
at `0x8004`, which are writable. -/
def frameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x50 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30 else 0
  rd := [⟨0x5000, 4168⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 16⟩]

theorem frameSat_pre (post : Spec.Blowfish.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Blowfish.ofbSig.contract X86.abi (post := post) (writeArgs := true) (stack := 112)).pre s := by
  implies_sat [Spec.Blowfish.ofbSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem fb_verified {w n : Nat} {post : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (fbX86 w n post).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (fbX86 w n post).post s s')
    (hct : ConstantTime isa (fbX86 w n post).pre (fbX86 w n post).pub c)
    (hR : ∀ s s' rd wr rd' wr', post (s.withRegions rd wr) (s'.withRegions rd' wr') → post s s')
    {k : Contract isa} (hi : (wideContract w n post).Implies k) : Verified X86.target c k := by
  have hsat := hi.sat_left
  have narrowSat : ∃ s, (fbX86 w n post).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre w n post s hs⟩
  apply Verified.of_implies _ hi
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat))
    narrowRd (narrowWr w) (wide_pre w n post) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    exact hR _ _ _ _ _ _ h
  · intro s₁ s₂ _ _ h
    narrow_blowfish_x86_fbverified
    exact h

theorem ofb_verified : Verified X86.target ofb (Proof.Blowfish.fbScratchContract X86.abi 11 Proof.Blowfish.ofbPost) :=
  fb_verified (fun _ hs => ofb_wp_x86 hs) ofb_ct (fun _ _ _ _ _ _ h => h) wide_implies_ofb

theorem cfbEncrypt_verified :
    Verified X86.target cfbEncrypt (Proof.Blowfish.fbScratchContract X86.abi 11 Proof.Blowfish.cfbEncPost) :=
  fb_verified (fun _ hs => cfbEncrypt_wp hs) cfbEncrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbEnc

theorem cfbDecrypt_verified :
    Verified X86.target cfbDecrypt (Proof.Blowfish.fbScratchContract X86.abi 11 Proof.Blowfish.cfbDecPost) :=
  fb_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbDec

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 ofb)
      (Spec.Blowfish.ofbContract X86.abi 112) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.ofbSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.ofbPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) ofb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.ofbPost_local _) (Proof.Blowfish.ofbPostOut_local _) (frameSat_pre _)

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 cfbEncrypt)
      (Spec.Blowfish.cfbEncryptContract X86.abi 112) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.cfbEncPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) cfbEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cfbEncPost_local _) (Proof.Blowfish.cfbEncPostOut_local _) (frameSat_pre _)

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 cfbDecrypt)
      (Spec.Blowfish.cfbDecryptContract X86.abi 112) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.cfbDecPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cfbDecPost_local _) (Proof.Blowfish.cfbDecPostOut_local _) (frameSat_pre _)

end VG.Proof.Blowfish.X86.Fb
