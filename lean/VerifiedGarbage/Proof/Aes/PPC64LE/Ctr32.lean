module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Group
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Group
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.ReadHalves
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Keys
meta import VerifiedGarbage.Proof.Framework.Bitslice.Sym
public import VerifiedGarbage.Proof.Aes.PPC64LE.Keys
public import VerifiedGarbage.Proof.Framework.Bitslice.Sym

/-!
# AES counter mode on PPC64LE: the whole function

The prologue saves the nonvolatile registers (checked by evaluation in the
naming domain, as is the epilogue restoring them), copies the counter block
to its slots and writes back the final counter; the key loop (`Keys.lean`)
and the group loop (`Group.lean`) do the rest.
-/

@[expose] public section

namespace VG.Proof.Aes

open Spec.Gcm

open VG.PPC64LE in
/-- PPC64LE contract for `vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize,
counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64;
256])`: XORs the AES counter-mode keystream from the counter block at `counter`
into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes, whose contents on
exit are unspecified). These may not overlap each other, and `data` may not
wrap around the end of the address space. `rounds` is 10, 12 or 14. The
pointers, `rounds` and `n` are public; the key schedule, the counter block and
the data are secret. -/
def ctr32PPC64LE : Contract PPC64LE.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 240⟩
    let counter : Region := ⟨s.gpr .r5, 16⟩
    let data : Region := ⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 2048⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .r6).toNat + 16 * (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .r4).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .r3) (16 * ((s.gpr .r4).toNat + 1)))
    blocksAt s'.mem (s.gpr .r6) (s.gpr .r7).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .r5)) (blocksAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) ∧
      blockAt s'.mem (s.gpr .r5) = Nat.repeat inc32 (s.gpr .r7).toNat (blockAt s.mem (s.gpr .r5))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Aes.PPC64LE VG.Proof.Aes

/-! ## Saving and restoring the nonvolatile registers -/

/-- The nonvolatile registers the code uses, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1)).getD i .r14)

def saveCfg : Cfg := { base := sb, slots := 58, ext := sb, exts := 0 }

def saveEnv : Env Nat :=
  { reg := fun r => (List.range 18).find? (fun i => sreg i == r), slot := fun _ => none }

def savePost (e : Env Nat) : Bool := (List.range 18).all fun i => e.slot (40 + i) == some i

theorem save_check : check (names 64) saveCfg (fun _ => none) saveRegs saveEnv savePost = true := by
  decide +kernel

def restoreEnv : Env Nat :=
  { reg := fun _ => none, slot := fun k => if 40 ≤ k ∧ k < 58 then some (k - 40) else none }

def restorePost (e : Env Nat) : Bool := (List.range 18).all fun i => e.reg (sreg i) == some i

theorem restore_check :
    check (names 64) saveCfg (fun _ => none) restoreRegs restoreEnv restorePost = true := by
  decide +kernel

theorem saveRegs_noDst : saveRegs.all (fun i => dstOf i == none) = true := by decide +kernel

/-- The registers `restoreRegs` writes are the saved ones. -/
theorem restoreRegs_dst : ∀ i ∈ restoreRegs, ∃ k < 18, dstOf i = some (sreg k) := by
  decide +kernel

theorem saveCfg_ok {s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hn : 8 * 58 ≤ n) (hn' : n < 2 ^ 64) : Ok saveCfg s :=
  Ok.of_region hw hb.symm hn hn' rfl

/-- The saved registers are in slots 40–57. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 18, m.readW (wordAddr b (40 + i)) 64 = s₀.gpr (sreg i)

theorem save_ok {s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hn : 8 * 58 ≤ n := by decide) (hn' : n < 2 ^ 64 := by decide) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * 58⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ save_check
  let V : Nat → BitVec 64 := fun i => s.gpr (sreg i)
  have hrel : Rel (NameRel V) saveCfg (fun _ => none) saveEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [saveCfg] at hk),
      fun _ _ h => by cases h⟩
    simp only [saveEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hw hb hn hn') hrel he
  refine ⟨s', hs', fun i hi => ?_, funext fun r => p.other r ?_, p.rd, p.wr, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot (40 + i) i (by simp [saveCfg]; omega_arith) this
    rw [p.base] at h
    simp only [saveCfg, hb] at h
    exact h
  · have : (saveRegs.all fun i => dstOf i != some r) = true :=
      List.all_eq_true.mpr fun i hi => by
        rw [beq_iff_eq.mp (List.all_eq_true.mp saveRegs_noDst i hi)]
        rfl
    simp [this]
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

theorem restore_ok {s₀ s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hs : Saved s₀ b s.mem) (hn : 8 * 58 ≤ n := by decide)
    (hn' : n < 2 ^ 64 := by decide) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 18, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * 58⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ restore_check
  let V : Nat → BitVec 64 := fun i => s₀.gpr (sreg i)
  have hrel : Rel (NameRel V) saveCfg (fun _ => none) restoreEnv s := by
    refine ⟨(fun r a h => by cases h), fun k a hk h => ?_, (fun _ _ hk _ => by simp [saveCfg] at hk),
      fun _ _ h => by cases h⟩
    simp only [restoreEnv] at h
    split at h
    · cases h
      rename_i hk'
      have := hs (k - 40) (by omega_arith)
      rw [show 40 + (k - 40) = k by omega_arith] at this
      simp only [NameRel, saveCfg, hb]
      exact this
    · cases h
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hw hb hn hn') hrel he
  refine ⟨s', hs', fun i hi => ?_, fun r hr => p.other r ?_, p.rd, p.wr, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    exact p.rel.reg _ i this
  · have : (restoreRegs.all fun i => dstOf i != some r) = true := by
      refine List.all_eq_true.mpr fun i hi => ?_
      obtain ⟨k, hk, he⟩ := restoreRegs_dst i hi
      rw [he]
      simpa using (hr k hk).symm
    simp [this]
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

theorem preserved_saved : ∀ r ∈ preserved, r = .r2 ∨ ∃ i < 18, r = sreg i := by decide

theorem sreg_ne_r2 : ∀ i < 18, sreg i ≠ .r2 := by decide

theorem sreg_ne_args : ∀ i < 18, sreg i ≠ .r6 ∧ sreg i ≠ .r7 ∧ sreg i ≠ .r8 := by decide

/-! ## The counter block -/

/-- The memory after `ctrSetup`: the counter block's slots, and the final
counter written back. -/
def setupMem (m : Mem) (b ctr : Addr) (N : BitVec 64) : Mem :=
  let m₁ := m.writeW (b + BitVec.ofNat 64 (8 * 58)) (m.readW ctr 64)
  let m₂ := m₁.writeW (b + BitVec.ofNat 64 (8 * 59))
    ((m₁.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64)
  let c := (rev32 (m₂.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64
  let m₃ := m₂.writeW (b + BitVec.ofNat 64 (8 * 60)) c
  m₃.writeW (ctr + BitVec.ofNat 64 12) (rev32 ((c + N).setWidth 32))

theorem ctrSetup_wp {s : State} {b ctr : Addr} (hb : s.gpr sb = b) (hc : s.gpr .r5 = ctr)
    (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) (hcw : (⟨ctr, 16⟩ : Region) ∈ s.wr) {P : State → Prop}
    (h : ∀ s', s'.mem = setupMem s.mem b ctr (s.gpr .r7) →
      (∀ r, r ≠ t0 → r ≠ .r0 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block ctrSetup) s P := by
  have hw' := List.mem_append_right s.rd hw
  have hcw' := List.mem_append_right s.rd hcw
  have l0 := in_off hcw' (off := 0) (n := 8) (by omega_arith) (by omega_arith)
  have l8 := in_off hcw' (off := 8) (n := 4) (by omega_arith) (by omega_arith)
  have l12 := in_off hcw' (off := 12) (n := 4) (by omega_arith) (by omega_arith)
  have w12 := in_off hcw (off := 12) (n := 4) (by omega_arith) (by omega_arith)
  have w58 := in_off hw (off := 8 * 58) (n := 8) (by omega_arith) (by omega_arith)
  have w59 := in_off hw (off := 8 * 59) (n := 8) (by omega_arith) (by omega_arith)
  have w60 := in_off hw (off := 8 * 60) (n := 8) (by omega_arith) (by omega_arith)
  simp only [BitVec.add_zero] at l0
  unfold ctrSetup stS cLo cHi cNum
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [hc]; exact BitVec.add_zero ctr) l0 fun s₁ u₁ => ?_
  refine wp_std (by decide) ⟨by decide, by decide⟩ (by rw [u₁.other _ (by decide), hb])
    (by rw [u₁.wr]; exact w58) fun s₂ u₂ => ?_
  refine wp_lwz (by decide) (by decide) (by rw [u₂.gpr, u₁.other _ (by decide), hc])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact l8) fun s₃ u₃ => ?_
  refine wp_std (by decide) ⟨by decide, by decide⟩
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hb])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact w59) fun s₄ u₄ => ?_
  refine wp_li (by decide) fun s₅ u₅ => ?_
  have r5₅ : s₅.gpr .r5 = ctr := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hc]
  refine wp_lwbrx (ea := ctr + BitVec.ofNat 64 12) (by decide) (by rw [r5₅, u₅.gpr])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact l12)
    fun s₆ u₆ => ?_
  refine wp_std (by decide) ⟨by decide, by decide⟩
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hb])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact w60) fun s₇ u₇ => ?_
  refine wp_add fun s₈ u₈ => ?_
  have r5₈ : s₈.gpr .r5 = ctr := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), r5₅]
  have r0₈ : s₈.gpr .r0 = BitVec.ofNat 64 12 := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.gpr]
  refine wp_stwbrx (ea := ctr + BitVec.ofNat 64 12) (by decide) (by rw [r5₈, r0₈])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact w12) fun s₉ u₉ => wp_nil ?_
  refine h s₉ ?_ (fun r h1 h2 => ?_) (by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd,
    u₁.rd]) (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₉.mem, u₈.gpr, u₈.mem, u₇.gpr, u₇.mem, u₆.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem,
      u₂.mem, u₁.gpr, u₁.mem, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
    rfl
  · rw [u₉.gpr, u₈.other _ h1, u₇.gpr, u₆.other _ h1, u₅.other _ h2, u₄.gpr, u₃.other _ h1, u₂.gpr,
      u₁.other _ h1]

theorem c_off (base : Addr) {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n :=
  Offset.contains_base base h ho

theorem out_of_disj {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) {x a : Addr} {n : Nat} (hx : r₁.Contains x 1)
    (ha : r₂.Contains a n) : ¬ (x - a).toNat < n := fun h => hd x hx (ha.byte h)

section Setup

variable {m : Mem} {b ctr : Addr} {N : BitVec 64}

theorem setupMem_eq (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    setupMem m b ctr N =
      (((m.writeW (b + BitVec.ofNat 64 (8 * 58)) (m.readW ctr 64)).writeW
        (b + BitVec.ofNat 64 (8 * 59)) ((m.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64)).writeW
        (b + BitVec.ofNat 64 (8 * 60)) ((rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64)).writeW
        (ctr + BitVec.ofNat 64 12)
          (rev32 (((rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 + N).setWidth 32)) := by
  have s8 : Mem.Sep (ctr + BitVec.ofNat 64 8) (32 / 8) (b + BitVec.ofNat 64 (8 * 58)) (64 / 8) :=
    hd.sep (c_off ctr (by omega_arith) (by omega_arith)) (c_off b (by omega_arith) (by omega_arith))
  have s12a : Mem.Sep (ctr + BitVec.ofNat 64 12) (32 / 8) (b + BitVec.ofNat 64 (8 * 58)) (64 / 8) :=
    hd.sep (c_off ctr (by omega_arith) (by omega_arith)) (c_off b (by omega_arith) (by omega_arith))
  have s12b : Mem.Sep (ctr + BitVec.ofNat 64 12) (32 / 8) (b + BitVec.ofNat 64 (8 * 59)) (64 / 8) :=
    hd.sep (c_off ctr (by omega_arith) (by omega_arith)) (c_off b (by omega_arith) (by omega_arith))
  simp only [setupMem]
  rw [Mem.readW_writeW_sep s8 (by decide), Mem.readW_writeW_sep s12b (by decide),
    Mem.readW_writeW_sep s12a (by decide)]

theorem setup_frame (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    Frame [⟨b + BitVec.ofNat 64 (8 * 58), 24⟩, ⟨ctr, 16⟩] m (setupMem m b ctr N) := by
  rw [setupMem_eq hd]
  have h₀ : (⟨b + BitVec.ofNat 64 (8 * 58), 24⟩ : Region) ∈
      [(⟨b + BitVec.ofNat 64 (8 * 58), 24⟩ : Region), ⟨ctr, 16⟩] := by simp
  have h₁ : (⟨ctr, 16⟩ : Region) ∈ [(⟨b + BitVec.ofNat 64 (8 * 58), 24⟩ : Region), ⟨ctr, 16⟩] := by
    simp
  exact ((((Frame.refl _ _).writeW h₀ _ (Offset.contains b (by omega_arith) (by omega_arith) (by omega_arith))).writeW h₀ _
    (Offset.contains b (by omega_arith) (by omega_arith) (by omega_arith))).writeW h₀ _
    (Offset.contains b (by omega_arith) (by omega_arith) (by omega_arith))).writeW h₁ _ (c_off ctr (by omega_arith) (by omega_arith))

theorem setup_slots (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    cloW (setupMem m b ctr N) b = m.readW ctr 64 ∧
    chiLo (setupMem m b ctr N) b = m.readW (ctr + BitVec.ofNat 64 8) 32 ∧
    numW (setupMem m b ctr N) b = (rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 := by
  rw [setupMem_eq hd]
  have t : ∀ {k w}, 8 * k + w / 8 ≤ 2048 → Mem.Sep (b + BitVec.ofNat 64 (8 * k)) (w / 8)
      (ctr + BitVec.ofNat 64 12) (32 / 8) := fun h =>
    hd.symm.sep (c_off b h (by omega_arith)) (c_off ctr (by omega_arith) (by omega_arith))
  refine ⟨?_, ?_, ?_⟩
  · rw [cloW, Mem.readW_writeW_sep (t (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [chiLo, Mem.readW_writeW_sep (t (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (d := 8 * 59) (n := 4) (e := 8 * 60) (k := 8) (by omega_arith)
        (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_lo32 (Mem.readW_writeW_self64 _ _ _)]
    simp
  · rw [numW, Mem.readW_writeW_sep (t (by omega_arith)) (by decide), Mem.readW_writeW_self64]

theorem setup_ctr (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) {k : Nat} (hk : k < 16) :
    setupMem m b ctr N (ctr + BitVec.ofNat 64 k) =
      if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (rev32 (((rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 + N).setWidth 32)).extractLsb'
        (8 * (k - 12)) 8 := by
  rw [setupMem_eq hd, writeW_apply, off_toNat ctr (by omega_arith) (by omega_arith)]
  have hx : (⟨ctr, 16⟩ : Region).Contains (ctr + BitVec.ofNat 64 k) 1 := c_off ctr (by omega_arith) (by omega_arith)
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega_arith), ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega_arith),
      ite_eq_left h, writeW_apply, ite_eq_right (out_of_disj hd hx (c_off b (by omega_arith) (by omega_arith))),
      writeW_apply, ite_eq_right (out_of_disj hd hx (c_off b (by omega_arith) (by omega_arith))),
      writeW_apply, ite_eq_right (out_of_disj hd hx (c_off b (by omega_arith) (by omega_arith)))]
  · rw [ite_eq_left (show 12 ≤ k by omega_arith), ite_eq_left (show k - 12 < 32 / 8 by omega_arith),
      ite_eq_right h, BitVec.setWidth_eq]

end Setup

/-! ## The counter block and the data, as blocks -/

theorem rev32_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (rev32 v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  rw [show rev32 = byteRev32 from rfl, byteRev32_getLsbD _ (by omega_arith),
    show (8 * k + j) / 8 = k by omega_arith, show (8 * k + j) % 8 = j by omega_arith]

/-- The counter, as the slot holds it. -/
theorem icb_lo (m : Mem) (ctr : Addr) :
    rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m ctr).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega_arith
  rw [e, rev32_bit _ (by omega_arith) (by omega_arith), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega_arith : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega_arith,
    blockAt_bit _ _ (by omega_arith) (by omega_arith)]
  have hb := Mem.readW_byte m (ctr + BitVec.ofNat 64 12) (i := 3 - t / 8) (by omega_arith)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 12 + (3 - t / 8) = 15 - t / 8 by omega_arith] at hb
  rw [hb, BitVec.getLsbD_extractLsb']
  simp [show t % 8 < 8 by omega_arith]

theorem ctr_after {m m' : Mem} {ctr : Addr} {n : Nat}
    (h : ∀ k < 16, m' (ctr + BitVec.ofNat 64 k) = if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (rev32 (((rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 +
        BitVec.ofNat 64 n).setWidth 32)).extractLsb' (8 * (k - 12)) 8) :
    Spec.Gcm.blockAt m' ctr = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m ctr) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, h k hk, ctrBlock_byte _ _ hk]
  split
  · rw [toBytes_blockAt _ _ hk]
  · rw [lo32_add, lo32_ext, setWidth_ofNat32, icb_lo]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', rev32_bit _ (by omega_arith) hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega_arith

theorem ctr32_of_dataInv {m₀ m : Mem} {D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : DataInv m₀ m D n n (keyStream R w icb)) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) icb (Spec.Gcm.blocksAt m₀ D n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine block_ext fun k hk => ?_
  rw [toBytes_xor _ _ hk, toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk, BitVec.add_assoc,
    ← BitVec.ofNat_add, h _ (by omega_arith), ite_eq_left (by omega_arith)]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [toBytes_ofBytes (by simp) hk, keyStream, show (16 * i + k) / 16 = i by omega_arith,
    show (16 * i + k) % 16 = k by omega_arith, getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-! ## Setting up the loops -/

theorem ofNat_shl4 {R : Nat} (h : R < 2 ^ 60) : BitVec.ofNat 64 R <<< 4 = BitVec.ofNat 64 (16 * R) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (a := R) (by omega)]
  congr 1; omega

theorem keySetup_wp {s : State} {R : Nat} (hR : s.gpr .r4 = BitVec.ofNat 64 R) (hR' : R ≤ 14)
    {P : State → Prop}
    (h : ∀ s', s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 (16 * R) →
      s'.gpr .r5 = s.gpr sb + BitVec.ofNat 64 1920 → s'.gpr .r4 = BitVec.ofNat 64 (R + 1) →
      (∀ r, r ≠ t0 → r ≠ .r3 → r ≠ .r5 → r ≠ .r4 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block keySetup) s P := by
  unfold keySetup lastKey
  refine wp_lsl (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => wp_addi (by decide) (by decide)
    fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ => wp_nil ?_
  refine h s₄ ?_ ?_ ?_ (fun r h1 h2 h3 h4 => ?_) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), u₁.gpr, hR,
      ofNat_shl4 (by omega)]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hR,
      BitVec.ofNat_add]
  · rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]

/-! ## The whole function -/

theorem saved_frame {s₀ : State} {b : Addr} {m m' : Mem} {rs : List Region} (h : Saved s₀ b m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 320, 144⟩ r) :
    Saved s₀ b m' := fun i hi => by
  rw [← h i hi]
  exact hf.readW (Offset.contains b (by omega_arith) (by omega_arith) (by omega_arith)) hd (by decide)

theorem notKeyWrites : ∀ r ∈ [Reg.r2, .r6, .r7, .r8], r ∉ keyWrites := by decide

theorem correct {s₀ : State} (hp : Proof.Aes.ctr32PPC64LE.pre s₀) :
    WP isa Impl.Aes.PPC64LE.ctr32 s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Aes.ctr32PPC64LE.post s₀ s' := by
  obtain ⟨hrd, hwr, dSC, dSD, dSS, dCD, dCS, dDS, hwrap, hR⟩ := hp
  have hwC : (⟨s₀.gpr .r5, 16⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwD : (⟨s₀.gpr .r6, 16 * (s₀.gpr .r7).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrS : (⟨s₀.gpr .r3, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have n16 : 16 * (s₀.gpr .r7).toNat < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dCD (s₀.gpr .r5) (by simp [Region.Contains]) ?_
    simp only [Region.Contains]
    have := (s₀.gpr .r5 - s₀.gpr .r6).isLt
    omega_arith
  have hR14 : (s₀.gpr .r4).toNat ≤ 14 := by omega_arith
  let b := s₀.gpr .r8
  let R := (s₀.gpr .r4).toNat
  let n := (s₀.gpr .r7).toNat
  -- The prologue.
  unfold Impl.Aes.PPC64LE.ctr32
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  obtain ⟨s₁, h₁, sv₁, g₁, rd₁, wr₁, f₁⟩ := save_ok hwS rfl
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  refine ctrSetup_wp (s := s₁) (b := b) (ctr := s₀.gpr .r5) (by rw [g₁]; rfl) (by rw [g₁])
    (wr₁ ▸ hwS) (wr₁ ▸ hwC) fun s₂ m₂ o₂ rd₂ wr₂ => ?_
  refine keySetup_wp (s := s₂) (R := R) (by rw [o₂ _ (by decide) (by decide), g₁]; simp [R]) hR14
    fun s₃ r3₃ r5₃ r4₃ o₃ m₃ rd₃ wr₃ => ?_
  -- Registers and memory after the prologue.
  have g₃ : ∀ r, r ≠ t0 → r ≠ .r0 → r ≠ .r3 → r ≠ .r5 → r ≠ .r4 → s₃.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₃ r h1 h3 h4 h5, o₂ r h1 h2, g₁]
  have hb₃ : s₃.gpr sb = b := g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have fS : Frame [⟨b + BitVec.ofNat 64 (8 * 58), 24⟩, ⟨s₀.gpr .r5, 16⟩] s₁.mem s₃.mem := by
    rw [m₃, m₂, g₁]; exact setup_frame dCS
  have f₀₃ : Frame [⟨b, 2048⟩, ⟨s₀.gpr .r5, 16⟩] s₀.mem s₃.mem := by
    refine (f₁.sub fun r hr => ⟨⟨b, 2048⟩, by simp, ?_⟩).trans (fS.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨b, 2048⟩, by simp, scr_sub _ (by omega_arith)⟩
      · exact ⟨⟨s₀.gpr .r5, 16⟩, by simp, fun _ h => h⟩
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .r3) (16 * (R + 1))
  have hk : KSetup s₃ b (s₀.gpr .r3) R w :=
    { scr := by rw [wr₃, wr₂, wr₁]; exact hwS
      base := hb₃
      sch := List.mem_append_left _ (by rw [rd₃, rd₂, rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₃.bytes (R := ⟨s₀.gpr .r3, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega_arith)).symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dSS
        · exact dSC }
  have hi₃ : KInv s₃ b (s₀.gpr .r3) R w R s₃ :=
    { hj := Nat.le_refl _
      r4 := r4₃
      r3 := by rw [r3₃, o₂ _ (by decide) (by decide), g₁]
      r5 := by rw [r5₃, o₂ _ (by decide) (by decide), g₁]; simp [keyAddr, sb, b]
      rd := rfl
      wr := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_arith) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₃) fun s₄ d₄ => ?_)
  refine WP.seq ?_
  unfold keyDone
  refine wp_addi (by decide) (by decide) fun s₅ u₅ => wp_nil ?_
  have g₅ : ∀ r ∈ [Reg.r2, .r6, .r7, .r8], s₅.gpr r = s₀.gpr r := fun r hr => by
    rw [u₅.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      d₄.keep r (notKeyWrites r hr)]
    simp at hr; rcases hr with rfl | rfl | rfl | rfl <;>
      exact g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hb₅ : s₅.gpr sb = b := g₅ .r8 (by simp)
  have hK0 : s₅.gpr .r3 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [u₅.gpr, d₄.r5]; exact BitVec.sub_add_cancel _ _
  have fK : Frame (kRegions b) s₃.mem s₅.mem := u₅.mem ▸ d₄.frame
  have kd : ∀ {x lx}, 320 ≤ x → x + lx ≤ 1024 → ∀ r ∈ kRegions b,
      Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h1 h2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  have cd : ∀ {x lx}, x + lx ≤ 16 → ∀ r ∈ [(⟨b, 8 * 58⟩ : Region)],
      Region.Disjoint ⟨s₀.gpr .r5 + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (dCS.sub_right (Region.sub_prefix (by omega_arith))).sub_left (Offset.sub_base _ h)
  obtain ⟨sl₁, sl₂, sl₃⟩ := setup_slots (m := s₁.mem) (N := s₁.gpr .r7) dCS
  rw [← m₂, ← m₃] at sl₁ sl₂ sl₃
  have clo₅ : cloW s₅.mem b = s₀.mem.readW (s₀.gpr .r5) 64 := by
    rw [cloW, fK.readW (Region.contains_self _ _) (kd (by omega_arith) (by omega_arith)) (by decide), ← cloW,
      sl₁]
    exact f₁.readW (r := ⟨s₀.gpr .r5, 16⟩) (by simp [Region.Contains]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dCS.sub_right (Region.sub_prefix (by omega_arith))) (by decide)
  have chi₅ : chiLo s₅.mem b = s₀.mem.readW (s₀.gpr .r5 + BitVec.ofNat 64 8) 32 := by
    rw [chiLo, fK.readW (Region.contains_self _ _) (kd (by omega_arith) (by omega_arith)) (by decide), ← chiLo, sl₂,
      f₁.readW (Region.contains_self _ _) (cd (by omega_arith)) (by decide)]
  have num₅ : numW s₅.mem b = (rev32 (s₀.mem.readW (s₀.gpr .r5 + BitVec.ofNat 64 12) 32)).setWidth 64 := by
    rw [numW, fK.readW (Region.contains_self _ _) (kd (by omega_arith) (by omega_arith)) (by decide), ← numW, sl₃,
      f₁.readW (Region.contains_self _ _) (cd (by omega_arith)) (by decide)]
  let icb := Spec.Gcm.blockAt s₀.mem (s₀.gpr .r5)
  have hs : GSetup s₅ b (s₀.gpr .r6) n R w icb :=
    { scr := by rw [u₅.wr, d₄.wr, wr₃, wr₂, wr₁]; exact hwS
      dat := by rw [u₅.wr, d₄.wr, wr₃, wr₂, wr₁]; exact hwD
      hn := n16
      sep := dDS
      rounds := hR
      keys := fun j hj => keyRel_congr (d₄.keys j hj) fun k hk => by
        rw [u₅.mem, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 1920 - 64 * R + 64 * j =
          1920 - 64 * (R - j) by omega_arith]
      lo := fun i hi j hj => by
        rw [clo₅, readW_bit _ _ hi hj, ← BitVec.add_zero (s₀.gpr .r5),
          blockAt_bit _ _ (by omega_arith) hj]
        simp
      hi := fun i hi j hj => by
        rw [chi₅, readW32_bit _ _ hi hj, show 8 * (7 - i) + j = 8 * (15 - (8 + i)) + j by omega_arith,
          blockAt_bit _ _ (by omega_arith) hj, BitVec.ofNat_add, ← BitVec.add_assoc] }
  -- The data is as on entry.
  have dd : ∀ r ∈ [(⟨b, 2048⟩ : Region), ⟨s₀.gpr .r5, 16⟩],
      Region.Disjoint ⟨s₀.gpr .r6, 16 * n⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dDS
    · exact dCD.symm
  have data₅ : DataInv s₀.mem s₅.mem (s₀.gpr .r6) n 0 (keyStream R w icb) :=
    dataInv_frame fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact dDS.sub_right (scr_sub _ (by omega_arith))) n16
      (dataInv_frame f₀₃ dd n16 fun i hi => by simp)
  refine WP.seq (WP.mono (Q := GDone s₀.mem s₅ b (s₀.gpr .r6) n R w icb) ?_ fun s₆ gd => ?_)
  · refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ (by omega_arith)
      (by rw [g₅ .r7 (by simp)]; simp [n])) (fun h0 => ?_) (fun h0 => ?_)
    · have hn0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨hb₅, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega_arith⟩
    · have hn0 : n ≠ 0 := by simpa using h0
      refine groups_ok hs ⟨by omega_arith, ?_, ?_, hb₅, hK0, rfl, rfl, rfl, Frame.refl _ _, ?_, data₅⟩
      · rw [g₅ _ (by simp)]; simp
      · rw [g₅ _ (by simp)]; simp [n]
      · rw [num₅, icb_lo]; simp [icb]
  -- The epilogue.
  have sv : Saved s₀ b s₆.mem := by
    refine saved_frame (saved_frame (saved_frame sv₁ fS ?_) fK ?_) gd.frame ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact (dCS.sub_right (scr_sub _ (by omega_arith))).symm
    · exact kd (by omega_arith) (by omega_arith)
    · intro r hr
      simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (scr_disj _ (by omega_arith) (by omega_arith)).symm
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact (dDS.sub_right (scr_sub _ (by omega_arith))).symm
  obtain ⟨s₇, h₇, rg₇, o₇, -, -, fR⟩ :=
    restore_ok (by rw [gd.wr, u₅.wr, d₄.wr, wr₃, wr₂, wr₁]; exact hwS) gd.base sv
  refine WP.of_runBlock ⟨s₇, h₇, ?_⟩
  have fsub : ∀ {x lx}, x + lx ≤ 2048 → Region.Sub ⟨b + BitVec.ofNat 64 x, lx⟩ ⟨b, 2048⟩ :=
    fun h => scr_sub _ h
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · rcases preserved_saved r hr with rfl | ⟨i, hi, rfl⟩
    · rw [o₇ _ (fun i hi => (sreg_ne_r2 i hi).symm), gd.r2]; exact g₅ .r2 (by simp)
    · exact rg₇ i hi
  · exact ctr32_of_dataInv (dataInv_frame fR (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dDS.sub_right (Region.sub_prefix (by omega_arith))) n16 gd.data)
  · refine ctr_after fun k hk => ?_
    have hC : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨s₀.gpr .r5, 16⟩ r) →
        m' (s₀.gpr .r5 + BitVec.ofNat 64 k) = m (s₀.gpr .r5 + BitVec.ofNat 64 k) :=
      fun hf hd => hf.bytes hd (by simp) hk
    rw [hC fR (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dCS.sub_right (Region.sub_prefix (by omega_arith))),
      hC gd.frame (fun r hr => by
        simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dCS.sub_right (Region.sub_prefix (by omega_arith))
        · exact dCS.sub_right (fsub (by omega_arith))
        · exact dCD),
      hC fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact dCS.sub_right (fsub (by omega_arith))),
      m₃, m₂, setup_ctr dCS hk, g₁,
      f₁.readW (Region.contains_self _ _) (cd (by omega_arith)) (by decide)]
    have e7 : BitVec.ofNat 64 (s₀.gpr .r7).toNat = s₀.gpr .r7 := by simp
    split
    · exact hC f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dCS.sub_right (Region.sub_prefix (by omega_arith))
    · rw [e7]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r7 => 1 | .r8 => 0x4000
    | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32PPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Aes.PPC64LE.ctr32 s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32PPC64LE.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by lit_decide) (by lit_decide)⟩, h₂⟩

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32PPC64LE.pre Proof.Aes.ctr32PPC64LE.pub
    Impl.Aes.PPC64LE.ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr32_verified :
    Verified PPC64LE.target Impl.Aes.PPC64LE.ctr32 (Spec.Gcm.ctr32Contract PPC64LE.abi) :=
  Verified.of_correct ctr32_correct ctr32_ct (by
    sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, Proof.Aes.ctr32PPC64LE, PPC64LE.abi,
      PPC64LE.argRegs] [Proof.Aes.PPC64LE.satState] using Proof.Aes.PPC64LE.satState)

end VG.Proof.Aes.PPC64LE
