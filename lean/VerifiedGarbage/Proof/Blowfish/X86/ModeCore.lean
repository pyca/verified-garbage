module

import VerifiedGarbage.Proof.Blowfish.X86.Ecb
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.Blowfish.X86.Modes
public import VerifiedGarbage.Proof.Blowfish.ModeBytes
public import VerifiedGarbage.Proof.Blowfish.X86.Cipher
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Blowfish's core for the modes on x86 (32-bit)

`dirCoreSpec up`: Blowfish's core encrypting (`up`) or decrypting
(`Impl.Blowfish.X86.dirCore up`) meets what the modes need of a core
(`Proof.Modes.X86.CoreSpec`), with the key the schedule at the address in the
first stack argument, read in place, its cipher `Spec.Blowfish.cipher` or
`Spec.Blowfish.invCipher` under it, and the key ready whenever that schedule
and its address are still there, apart from every writable region (`Ready`):
`prepare` does nothing.
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
  have hea : s'.ea (at_ .esp 4) = s.ea (at_ .esp 4) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨by rw [hrd, hwr, hea]; exact hin, ?_, ?_, by rw [hrd, hwr]; exact hsch, hfit⟩
  · rw [hea, hf.readW (Region.contains_self _ _) (fun r hr => (ha r hr).2) (by decide), hv]
  · rw [hk, scheduleAt_eq_of_frame _ hf fun r hr => (ha r hr).1]

theorem Ready.frame {s s' : State} {k : Schedule} {rs : List Region} (h : Ready s k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r') : Ready s' k := by
  obtain ⟨S, hS, ha⟩ := h
  have hea : s'.ea (at_ .esp 4) = s.ea (at_ .esp 4) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  exact ⟨S, hS.frame (ha.sub hs) hesp hrd hwr hf, by rw [hwr, hea]; exact ha⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨S, hS, ha, hw⟩ := h
  have hea : s'.ea (at_ .esp 4) = s.ea (at_ .esp 4) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  exact ⟨S, hS.frame ha hesp hrd hwr hf, by rw [hea]; exact ha, by rw [hwr, hea]; exact hw⟩

/-! ## The block -/

theorem addr_slot48 {B : BitVec 32} (h : B.toNat + 48 ≤ 2 ^ 32) {d : Nat} (hd : d < 48) :
    addr B d = slot B d := addr_of_fit (by omega)

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
  have e : ∀ v : BitVec 32, (u.mem.writeW (slot B 40) v).readW (slot B 20) 32 = u.mem.readW (slot B 20) 32 :=
    fun v => Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  unfold modeStore
  brun [bufOff, hb, addr_slot48 bfit, r16, r20, w40, w44, e]

/-- The block stored as two big-endian words. -/
theorem stored_block (m : Mem) (Pa : Addr) (L R : BitVec 32) :
    blockAt ((m.writeW Pa (bswap L)).writeW (Pa + BitVec.ofNat 64 4) (bswap R)) Pa = encodeBlock L R := by
  refine blockAt_eq _ _ _ fun i hi => ?_
  rw [encodeBlock_getD _ _ hi]
  by_cases h4 : i < 4
  · rw [ite_eq_left h4, writeW32_other _ (Offset.disjoint Pa (d := i) (n := 1) (e := 4) (k := 4) (by omega)
      (by omega) (by decide)), st_byte _ _ _ h4, bswap_byte _ h4]
  · rw [ite_eq_right h4, show i = 4 + (i - 4) by omega, ← Offset.add_add, st_byte _ _ _ (by omega),
      bswap_byte _ (by omega)]
    congr 2; omega

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
  have bfit : B.toNat + 48 ≤ 2 ^ 32 := by omega
  have scr : (⟨B.setWidth 64, 88⟩ : Region) ∈ s.wr := hs.wr
  have hea : s.ea (at_ .esp 4) = addr (s.gpr .esp) 4 := rfl
  have wS : ∀ d, d + 4 ≤ 48 → InRegions s.wr (slot B d) 4 := fun d hd =>
    ⟨_, scr, Offset.contains_base _ (by omega) (by omega)⟩
  have core48 : Region.Sub ⟨B.setWidth 64, 48⟩ ⟨B.setWidth 64, 88⟩ := Region.sub_prefix (by decide)
  have aS := (ha _ scr).1
  have aA := (ha _ scr).2
  let Pa := slot B 40
  have e44 : Pa + BitVec.ofNat 64 4 = slot B 44 := Offset.add_add _ _ _
  show WP isa (.seq (.block (modeSetup ++ loadBlock)) (.seq (cipher 4 up) (.block modeStore))) s _
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.ebp, .ebx] (setup_run s hB' bfit (wS 32 (by decide))) (by decide))
    fun u₁ ⟨⟨m₁, bp₁⟩, k₁⟩ => ?_
  have wr₁ : u₁.wr = s.wr := k₁.2.2
  have rd₁ : u₁.rd = s.rd := k₁.2.1
  have w₁ : ∀ d, d + 4 ≤ 48 → InRegions u₁.wr (slot B d) 4 := fun d hd => by rw [wr₁]; exact wS d hd
  have e0 : addr (B + BitVec.ofNat 32 40) 0 = Pa := by
    unfold addr; rw [ofs_add, ← addr, addr_slot48 bfit (by decide)]
  have e4 : addr (B + BitVec.ofNat 32 40) 4 = Pa + BitVec.ofNat 64 4 := by
    unfold addr; rw [ofs_add, ← addr, addr_slot48 bfit (by decide), e44]
  refine WP.mono (WP.keep [.eax, .ebx] (loadBlock_run u₁ (B := B) bp₁ (by omega) (w₁ 16 (by decide))
    (w₁ 20 (by decide)) (region_in (w₁ 32 (by decide)))
    (by rw [m₁, Mem.readW_writeW_self32]) e0 e4 (region_in (w₁ 40 (by decide)))
    (by rw [e44]; exact region_in (w₁ 44 (by decide)))
    (by rw [e44]; exact Offset.sep _ (by decide) (by decide) (by decide))) (by decide))
    fun u₂ ⟨m₂, k₂⟩ => ?_
  have k₁₂ : Keep [.ebp, .ebx, .eax] s u₂ := (k₁.trans k₂).mono (by decide)
  have esp₂ : u₂.gpr .esp = s.gpr .esp := k₁₂.gpr (by decide)
  have F₂ : Frame [⟨B.setWidth 64, 48⟩] s.mem u₂.mem := by
    rw [m₂, m₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 32) (n := 4)
      (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 16) (n := 4)
      (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 20) (n := 4)
      (by decide) (by decide))
  have wide : ∀ {m m' : Mem}, Frame [⟨B.setWidth 64, 48⟩] m m' → Frame [⟨B.setWidth 64, 88⟩] m m' := fun hf =>
    hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, core48⟩
  have apS : Apart S (s.ea (at_ .esp 4)) [⟨B.setWidth 64, 88⟩] := ha.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, scr, fun _ h => h⟩
  -- the block in, as the halves
  have blk₁ : blockAt u₁.mem Pa = blockAt s.mem Pa := by
    rw [m₁]
    exact blockAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by decide) (by decide) (by decide)
  -- the cipher
  have CE : CipherEnv 4 S B u₂ := by
    refine ⟨(k₂.gpr (by decide)).trans bp₁, by omega, ?_, ?_, ?_, hSfit, fun o ho => ?_, ?_, ?_⟩
    · rw [k₂.2.2, wr₁]; exact ⟨_, scr, contains_pre _ (by decide)⟩
    · rw [keep_reads k₁₂, esp₂, ← hea]; exact hin
    · rw [esp₂, ← hea, (wide F₂).readW (Region.contains_self _ _) (fun r hr => (apS r hr).2) (by decide)]; exact hv
    · rw [keep_reads k₁₂]; exact ⟨_, hsch, Offset.contains_base _ (by omega) (by omega)⟩
    · exact aS.symm.sub_left (Region.sub_prefix (by decide))
    · rw [esp₂, ← hea]; exact aA.symm.sub_left (Region.sub_prefix (by decide))
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun u₃ ⟨c₃, ck₃, cf₃⟩ => ?_
  have k₃ : Keep [.ebp, .ebx, .eax, .ecx, .edx, .esi, .edi] s u₃ := (k₁₂.trans ck₃).mono (by decide)
  have F₃ : Frame [⟨B.setWidth 64, 48⟩] s.mem u₃.mem :=
    F₂.trans (cf₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)
  have w₃ : ∀ d, d + 4 ≤ 48 → InRegions u₃.wr (slot B d) 4 := fun d hd => by rw [k₃.2.2]; exact wS d hd
  -- the block out
  refine WP.mono (WP.keep [.eax, .edi] (store_run u₃ ((ck₃.gpr (by decide)).trans CE.bp) bfit
    (region_in (w₃ 16 (by decide))) (region_in (w₃ 20 (by decide))) (w₃ 40 (by decide)) (w₃ 44 (by decide))) (by
      decide))
    fun u₄ ⟨⟨m₄, di₄⟩, k₄⟩ => ?_
  have k₄' : Keep [.ebp, .ebx, .eax, .ecx, .edx, .esi, .edi] s u₄ := (k₃.trans k₄).mono (by decide)
  have esp₄ : u₄.gpr .esp = s.gpr .esp := k₄'.gpr (by decide)
  have F₄ : Frame [⟨B.setWidth 64, 48⟩] s.mem u₄.mem := by
    rw [m₄]
    exact (F₃.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 40) (n := 4) (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 44) (n := 4) (by decide)
      (by decide))
  have rd₄ : u₄.rd = s.rd := k₄'.2.1
  have wr₄ : u₄.wr = s.wr := k₄'.2.2
  have hS : SchedAt s k S := ⟨hin, hv, hk, hsch, hSfit⟩
  refine ⟨di₄, esp₄, ⟨S, hS.frame apS esp₄ rd₄ wr₄ (wide F₄),
      by rw [wr₄, show u₄.ea (at_ .esp 4) = s.ea (at_ .esp 4) by
        show (u₄.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [esp₄]]; exact ha⟩,
    F₄.sub fun r hr => ?_, fun j hj => ?_, rd₄, wr₄⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · obtain rfl : j = 0 := by simp only [dirCore] at hj; omega
    have hba : blkAddr (dirCore up) B 0 = Pa := by
      simp only [blkAddr, slotA, dirCore, Offset.add_add]; rfl
    have e16 : u₂.mem.readW (slot B 16) 32 = decodeWord (blockAt u₁.mem Pa) 0 := by
      rw [m₂, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32]
    have e20 : u₂.mem.readW (slot B 20) 32 = decodeWord (blockAt u₁.mem Pa) 4 := by
      rw [m₂, Mem.readW_writeW_self32]
    rw [e16, e20, blk₁] at c₃
    have hK : scheduleAt u₂.mem (S.setWidth 64) = k := by
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
  layout := ⟨by simp only [dirCore]; decide, .inl rfl, by simp only [dirCore]; omega,
    by simp only [dirCore]; omega⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h e r w _ hf hs _ := ⟨h.1.frame e r w hf hs, h.2⟩
  prepare_wp hB hs _ hk _ := by
    obtain ⟨S, hS, -, hw⟩ := hk
    refine WP.block_nil ⟨⟨⟨S, hS, hw⟩, hs.fit⟩, hB, rfl, Frame.refl _ _, rfl, rfl⟩
  crypt_wp hB hs hr _ := WP.mono (crypt_wp up hB hs hr.1) fun _ ⟨b, e, r, h⟩ => ⟨b, e, ⟨r, hr.2⟩, h⟩

end VG.Proof.Blowfish.X86
