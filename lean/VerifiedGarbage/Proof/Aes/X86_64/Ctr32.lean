module

public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Aes.X86_64.Group
public import VerifiedGarbage.Impl.Aes.X86_64.Sse
meta import VerifiedGarbage.Impl.Aes.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Aes.X86_64.Group
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Aes.X86_64.Sse.Group
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds

/-!
# AES counter mode on x86-64: the whole function

The prologue saves the callee-saved registers (checked by evaluation in the
naming domain, as is the epilogue restoring them), copies the counter block
to its slots and writes back the final counter; the key loop (`Group.lean`),
the masks of ShiftRows and the loop over groups of four and of eight blocks
(`Sse/Group.lean`) do the rest.

One proof covers `vg_aes_ctr32` and its out-of-place form `vg_aes_ctr32_to`
(`correct`, over `CPre`): the groups read the source at `rcx` and write the
output at `dOut`, the same in place. Out of place, the output pointer waits
in `xmm15` through the key loop, which writes no SSE register (`WP.xkeep`),
and then lives in its slot of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Aes

open Spec.Gcm

open VG.X86_64 in
/-- X86-64 contract for `vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize,
counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64;
256])`: XORs the AES counter-mode keystream from the counter block at `counter`
into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the return
address on the stack, and `data` may not wrap around the end of the address
space. `rounds` is 10, 12 or 14. The pointers, `rounds` and `n` are public;
the key schedule, the counter block and the data are secret. -/
def ctr32X86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let counter : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 2048⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint counter ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .rsi).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1)))
    blocksAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .rdx)) (blocksAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) ∧
      blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 (s.gpr .r8).toNat (blockAt s.mem (s.gpr .rdx))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- X86-64 contract for `vg_aes_expand_key(key: *const u8, key_len: usize,
schedule: *mut [u8; 240], scratch: *mut [u64; 64])`: writes the key schedule of
the `key_len`-byte key at `key` to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes, whose contents on exit are
unspecified). These may not overlap each other, and the writable ones may not
overlap the return address on the stack. `key_len` is 16, 24 or 32. The
pointers and `key_len` are public; the key is secret. -/
def expandKeyX86_64 : Contract X86_64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let sched : Region := ⟨s.gpr .rdx, 240⟩
    let scratch : Region := ⟨s.gpr .rcx, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    ret.Disjoint sched ∧ ret.Disjoint scratch ∧
    ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) (16 * (Spec.Aes.rounds ((s.gpr .rsi).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Aes

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64 VG.Proof.Aes

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg : Nat → Reg
  | 0 => .rbx | 1 => .rbp | 2 => .r12 | 3 => .r13 | 4 => .r14 | _ => .r15

def saveCfg : Cfg := { base := sb, slots := 54, ext := sb, exts := 0 }

def saveEnv : Env Nat :=
  { reg := fun r => (List.range 6).find? (fun i => sreg i == r), slot := fun _ => none }

def savePost (e : Env Nat) : Bool := (List.range 6).all fun i => e.slot (48 + i) == some i

theorem save_check : check (names 64) saveCfg (fun _ => none) saveRegs saveEnv savePost = true := by
  decide +kernel

def restoreEnv : Env Nat :=
  { reg := fun _ => none, slot := fun k => if 48 ≤ k ∧ k < 54 then some (k - 48) else none }

def restorePost (e : Env Nat) : Bool := (List.range 6).all fun i => e.reg (sreg i) == some i

theorem restore_check :
    check (names 64) saveCfg (fun _ => none) restoreRegs restoreEnv restorePost = true := by
  decide +kernel

theorem saveCfg_ok {s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hn : 8 * 54 ≤ n) : Ok saveCfg s :=
  Ok.of_region hw hb.symm hn (by simp [saveCfg]) rfl

/-- The saved registers are in slots 48–53. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 6, m.readW (wordAddr b (48 + i)) 64 = s₀.gpr (sreg i)

theorem save_ok {s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hn : 8 * 54 ≤ n) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * 54⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ save_check
  let V : Nat → BitVec 64 := fun i => s.gpr (sreg i)
  have hrel : Rel (NameRel V) saveCfg (fun _ => none) saveEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [saveCfg] at hk)⟩
    simp only [saveEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hw hb hn) hrel he
  refine ⟨s', hs', fun i hi => ?_, funext fun r => p.other r ?_, p.rd, p.wr, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot (48 + i) i (by simp [saveCfg]; omega_arith) this
    rw [p.base] at h
    simp only [saveCfg, hb] at h
    exact h
  · have : (saveRegs.all fun i => i.dst != some r) = true := by simp [saveRegs, savedRegs, st, reduceInstrDst]
    simp [this]
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

theorem restore_ok {s₀ s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hn : 8 * 54 ≤ n) (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 6, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 6, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧
      Frame [⟨b, 8 * 54⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ restore_check
  let V : Nat → BitVec 64 := fun i => s₀.gpr (sreg i)
  have hrel : Rel (NameRel V) saveCfg (fun _ => none) restoreEnv s := by
    refine ⟨(fun r a h => by cases h), fun k a hk h => ?_, (fun _ _ hk _ => by simp [saveCfg] at hk)⟩
    simp only [restoreEnv] at h
    split at h
    · cases h
      rename_i hk'
      have := hs (k - 48) (by omega_arith)
      rw [show 48 + (k - 48) = k by omega_arith] at this
      simp only [NameRel, saveCfg, hb]
      exact this
    · cases h
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hw hb hn) hrel he
  refine ⟨s', hs', fun i hi => ?_, fun r hr => p.other r ?_, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    exact p.rel.reg _ i this
  · have : (restoreRegs.all fun i => i.dst != some r) = true := by
      have h0 := hr 0 (by omega_arith); have h1 := hr 1 (by omega_arith); have h2 := hr 2 (by omega_arith)
      have h3 := hr 3 (by omega_arith); have h4 := hr 4 (by omega_arith); have h5 := hr 5 (by omega_arith)
      simp only [sreg] at h0 h1 h2 h3 h4 h5
      simp [restoreRegs, savedRegs, movS, reduceInstrDst, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3,
        Ne.symm h4, Ne.symm h5]
    simp [this]
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

/-! ## The counter block -/

/-- The memory after `ctrSetup`: the counter block's slots, and the final
counter written back. -/
def setupMem (m : Mem) (b ctr : Addr) (N : BitVec 64) : Mem :=
  let m₁ := m.writeW (b + BitVec.ofNat 64 (8 * 54)) (m.readW (ctr + BitVec.ofNat 64 0) 64)
  let m₂ := m₁.writeW (b + BitVec.ofNat 64 (8 * 55))
    ((m₁.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64)
  let c := bswap32 (m₂.readW (ctr + BitVec.ofNat 64 12) 32)
  let m₃ := m₂.writeW (b + BitVec.ofNat 64 (8 * 56)) c
  m₃.writeW (ctr + BitVec.ofNat 64 12) (bswap32 (c + N.setWidth 32))

theorem ctrSetup_ok {s : State} {b ctr : Addr} (hb : s.gpr sb = b) (hc : s.gpr .rdx = ctr)
    (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) (hcw : (⟨ctr, 16⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa ctrSetup s = some s' ∧ s'.mem = setupMem s.mem b ctr (s.gpr .r8) ∧
      s'.gpr .rdx = s.gpr .rcx ∧ (∀ r, r ≠ .rax → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw' := List.mem_append_right s.rd hw
  have hcw' := List.mem_append_right s.rd hcw
  have l0 := in_off hcw' (off := 0) (n := 8) (by omega_arith) (by omega_arith)
  have l8 := in_off hcw' (off := 8) (n := 4) (by omega_arith) (by omega_arith)
  have l12 := in_off hcw' (off := 12) (n := 4) (by omega_arith) (by omega_arith)
  have w12 := in_off hcw (off := 12) (n := 4) (by omega_arith) (by omega_arith)
  have w54 := in_off hw (off := 8 * 54) (n := 8) (by omega_arith) (by omega_arith)
  have w55 := in_off hw (off := 8 * 55) (n := 8) (by omega_arith) (by omega_arith)
  have w56 := in_off hw (off := 8 * 56) (n := 4) (by omega_arith) (by omega_arith)
  refine ⟨_, by
    simp (config := {decide := true}) only [ctrSetup, movR, st, at_, slotAt, cLo, cHi, cNum,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc, readSrc32, State.load64,
      State.load32, State.store64, State.store32, State.ea, ofInt_nat, State.setReg32, State.setReg,
      State.setFlags, arithFlags, hb, hc, ite_false, ite_true, l0, l8, l12, w12, w54, w55, w56,
      Option.map_some, Option.bind_some, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨rfl, by simp, fun r h1 h2 => by simp [h1, h2], rfl, rfl⟩

theorem c_off (base : Addr) {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n :=
  Offset.contains_base base h ho

theorem out_of_disj {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) {x a : Addr} {n : Nat} (hx : r₁.Contains x 1)
    (ha : r₂.Contains a n) : ¬ (x - a).toNat < n := fun h => hd x hx (ha.byte h)

section Setup

variable {m : Mem} {b ctr : Addr} {N : BitVec 64}

theorem setupMem_eq (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    setupMem m b ctr N =
      (((m.writeW (b + BitVec.ofNat 64 (8 * 54)) (m.readW (ctr + BitVec.ofNat 64 0) 64)).writeW
        (b + BitVec.ofNat 64 (8 * 55)) ((m.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64)).writeW
        (b + BitVec.ofNat 64 (8 * 56)) (bswap32 (m.readW (ctr + BitVec.ofNat 64 12) 32))).writeW
        (ctr + BitVec.ofNat 64 12)
          (bswap32 (bswap32 (m.readW (ctr + BitVec.ofNat 64 12) 32) + N.setWidth 32)) := by
  have s8 : Mem.Sep (ctr + BitVec.ofNat 64 8) (32 / 8) (b + BitVec.ofNat 64 (8 * 54)) (64 / 8) :=
    hd.sep (c_off ctr (by omega_arith) (by omega_arith)) (c_off b (by omega_arith) (by omega_arith))
  have s12a : Mem.Sep (ctr + BitVec.ofNat 64 12) (32 / 8) (b + BitVec.ofNat 64 (8 * 54)) (64 / 8) :=
    hd.sep (c_off ctr (by omega_arith) (by omega_arith)) (c_off b (by omega_arith) (by omega_arith))
  have s12b : Mem.Sep (ctr + BitVec.ofNat 64 12) (32 / 8) (b + BitVec.ofNat 64 (8 * 55)) (64 / 8) :=
    hd.sep (c_off ctr (by omega_arith) (by omega_arith)) (c_off b (by omega_arith) (by omega_arith))
  simp only [setupMem]
  rw [Mem.readW_writeW_sep s8 (by decide), Mem.readW_writeW_sep s12b (by decide),
    Mem.readW_writeW_sep s12a (by decide)]

theorem setup_frame (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    Frame [⟨b + BitVec.ofNat 64 (8 * 54), 20⟩, ⟨ctr, 16⟩] m (setupMem m b ctr N) := by
  rw [setupMem_eq hd]
  have h₀ : (⟨b + BitVec.ofNat 64 (8 * 54), 20⟩ : Region) ∈
      [(⟨b + BitVec.ofNat 64 (8 * 54), 20⟩ : Region), ⟨ctr, 16⟩] := by simp
  have h₁ : (⟨ctr, 16⟩ : Region) ∈ [(⟨b + BitVec.ofNat 64 (8 * 54), 20⟩ : Region), ⟨ctr, 16⟩] := by
    simp
  exact ((((Frame.refl _ _).writeW h₀ _ (off_contains b (by omega_arith) (by omega_arith) (by omega_arith))).writeW h₀ _
    (off_contains b (by omega_arith) (by omega_arith) (by omega_arith))).writeW h₀ _
    (off_contains b (by omega_arith) (by omega_arith) (by omega_arith))).writeW h₁ _ (c_off ctr (by omega_arith) (by omega_arith))

theorem setup_slots (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    cloW (setupMem m b ctr N) b = m.readW (ctr + BitVec.ofNat 64 0) 64 ∧
    chiW (setupMem m b ctr N) b = (m.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64 ∧
    numW (setupMem m b ctr N) b = bswap32 (m.readW (ctr + BitVec.ofNat 64 12) 32) := by
  rw [setupMem_eq hd]
  have t : ∀ {k w}, 8 * k + w / 8 ≤ 2048 → Mem.Sep (b + BitVec.ofNat 64 (8 * k)) (w / 8)
      (ctr + BitVec.ofNat 64 12) (32 / 8) := fun h =>
    hd.symm.sep (c_off b h (by omega_arith)) (c_off ctr (by omega_arith) (by omega_arith))
  refine ⟨?_, ?_, ?_⟩
  · rw [cloW, Mem.readW_writeW_sep (t (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [chiW, Mem.readW_writeW_sep (t (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [numW, Mem.readW_writeW_sep (t (by omega_arith)) (by decide), Mem.readW_writeW_self32]

theorem writeW_apply {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) :
    m.writeW a v x = if (x - a).toNat < w / 8 then
      (v.setWidth (8 * (w / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

theorem setup_ctr (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) {k : Nat} (hk : k < 16) :
    setupMem m b ctr N (ctr + BitVec.ofNat 64 k) =
      if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (bswap32 (bswap32 (m.readW (ctr + BitVec.ofNat 64 12) 32) + N.setWidth 32)).extractLsb'
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

/-- The counter, as the slot holds it. -/
theorem icb_lo (m : Mem) (ctr : Addr) :
    bswap32 (m.readW (ctr + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m ctr).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega_arith
  rw [e, bswap32_bit _ (by omega_arith) (by omega_arith), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega_arith : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega_arith,
    blockAt_bit _ _ (by omega_arith) (by omega_arith)]
  have hb := Mem.readW_byte m (ctr + BitVec.ofNat 64 12) (i := 3 - t / 8) (by omega_arith)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 12 + (3 - t / 8) = 15 - t / 8 by omega_arith] at hb
  rw [hb, BitVec.getLsbD_extractLsb']
  simp [show t % 8 < 8 by omega_arith]

theorem ctr_after {m m' : Mem} {ctr : Addr} {n : Nat}
    (h : ∀ k < 16, m' (ctr + BitVec.ofNat 64 k) = if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (bswap32 (bswap32 (m.readW (ctr + BitVec.ofNat 64 12) 32) +
        (BitVec.ofNat 64 n).setWidth 32)).extractLsb' (8 * (k - 12)) 8) :
    Spec.Gcm.blockAt m' ctr = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m ctr) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, h k hk, ctrBlock_byte _ _ hk]
  split
  · rw [toBytes_blockAt _ _ hk]
  · rw [icb_lo, show (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n by
      apply BitVec.eq_of_toNat_eq; simp]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', bswap32_bit _ (by omega_arith) hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega_arith

theorem ctr32_of_dataInv {m₀ m : Mem} {S D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : DataInv m₀ m S D n n (keyStream R w icb)) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) icb (Spec.Gcm.blocksAt m₀ S n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine block_ext fun k hk => ?_
  rw [toBytes_xor _ _ hk, toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk, BitVec.add_assoc,
    ← BitVec.ofNat_add, h _ (by omega_arith), ite_eq_left (by omega_arith), BitVec.add_assoc, ← BitVec.ofNat_add]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [toBytes_ofBytes (by simp) hk, keyStream, show (16 * i + k) / 16 = i by omega_arith,
    show (16 * i + k) % 16 = k by omega_arith, getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-! ## The SSE registers through code that writes none -/

theorem xmm_block : ∀ {is : List Instr} {s t : State}, is.all (fun i => !KeepReg.writesVec i) = true →
    runBlock isa is s = some t → t.xmm = s.xmm
  | [], _, _, _, he => by cases he; rfl
  | i :: is, s, t, hi, he => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
    rw [runBlock_cons] at he
    cases hs : exec i s with
    | none => rw [hs] at he; cases he
    | some u =>
      rw [hs, runStep_some] at he
      exact (xmm_block hi.2 he).trans (KeepReg.exec_xmm hi.1 hs)

theorem xmm_code {c : Prog isa} {s t : State} {tr : List Leak} (he : Exec isa c s tr t)
    (hn : c.noCalls = true) (hi : c.all (fun i => !KeepReg.writesVec i) = true) : t.xmm = s.xmm := by
  induction he with
  | icall | icallNext => simp [Code.noCalls] at hn
  | block hb =>
    rename_i is s t tr
    have hw : WP isa (.block is) s (fun u => u = t) := ⟨tr, t, .block hb, rfl⟩
    obtain ⟨u, hu, rfl⟩ := WP.runBlock_of hw
    exact xmm_block hi hu
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.noCalls, Code.all, Bool.and_eq_true] at hn hi
    exact (ih₂ hn.2 hi.2).trans (ih₁ hn.1 hi.1)
  | iteT _ _ ih =>
    simp only [Code.noCalls, Code.all, Bool.and_eq_true] at hn hi
    exact ih hn.1 hi.1
  | iteF _ _ ih =>
    simp only [Code.noCalls, Code.all, Bool.and_eq_true] at hn hi
    exact ih hn.2 hi.2
  | loopExit _ _ ih => exact ih hn hi
  | loopNext _ _ _ ih₁ ih₂ => exact (ih₂ hn hi).trans (ih₁ hn hi)
  | call => simp [Code.noCalls] at hn
  | frame => simp [Code.noCalls] at hn

theorem WP.xkeep {c : Prog isa} {s : State} {Q : State → Prop}
    (hn : c.noCalls = true) (hi : c.all (fun i => !KeepReg.writesVec i) = true) (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.xmm = s.xmm := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, hq, xmm_code he hn hi⟩

/-! ## The output pointer, out of place -/

theorem dstStash_wp (to : Bool) {s : State} {P : State → Prop}
    (h : ∀ s', (to = true → (s'.xmm .xmm15).extractLsb' 0 64 = s.gpr .r11) → s'.gpr = s.gpr →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (dstStash to)) s P := by
  cases to
  · exact WP.block_nil (h s (by simp) rfl rfl rfl rfl)
  · refine WP.of_runBlock ⟨_, by
      simp only [dstStash, ite_true, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec]
      rfl, ?_⟩
    refine h _ (fun _ => ?_) rfl rfl rfl rfl
    simp only [VG.X86_64.RegUpd.xmm_setXmm_self]
    ext k hk; simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [hk]

theorem dstInit_wp (to : Bool) {s : State} {b : Addr} (hb : s.gpr sb = b)
    (hscr : (⟨b, 2048⟩ : Region) ∈ s.wr) {P : State → Prop}
    (h : ∀ s', (to = true → s'.mem.readW (dAddr b) 64 = (s.xmm .xmm15).extractLsb' 0 64) →
      (∀ r, r ≠ t1 → s'.gpr r = s.gpr r) → Frame [dRegion b] s.mem s'.mem →
      s'.xmm = s.xmm → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (dstInit to)) s P := by
  cases to
  · exact WP.block_nil (h s (by simp) (fun _ _ => rfl) (Frame.refl _ _) rfl rfl rfl)
  · have hin := dSlot_in hscr
    have hsb : sb ≠ t1 := by decide
    refine WP.of_runBlock ⟨_, by
      simp only [dstInit, ite_true, st, slotAt, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
        State.store64, State.ea, ofInt_nat, VG.X86_64.RegUpd.gpr_setReg_of_ne _ _ hsb, hb,
        VG.X86_64.RegUpd.wr_setReg, show b + BitVec.ofNat 64 (8 * dSlot) = dAddr b from rfl, hin, ite_true]
      rfl, ?_⟩
    refine h _ (fun _ => ?_) (fun r hr => by simp [State.setReg, hr]) ?_ rfl rfl rfl
    · show ((s.setReg t1 _).mem.writeW (dAddr b) ((s.setReg t1 _).gpr t1)).readW (dAddr b) 64 = _
      rw [Mem.readW_writeW_self (n := 8) _ _ _ (by decide)]
      simp [State.setReg]
    · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## Setting up the loops -/

theorem keySetup_ok (s : State) :
    ∃ s', runBlock isa keySetup s = some s' ∧ s'.gpr .r15 = s.gpr .rsi ∧
      s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rsi = s.gpr sb + BitVec.ofNat 64 1920 ∧
      (∀ r, r ≠ .r15 → r ≠ .rdi → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [keySetup, movR, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, Option.bind_some, Option.map_some]; rfl, ?_⟩
  simp only [State.setReg, arithFlags, State.setFlags]
  refine ⟨by simp, ?_, ?_, fun r h1 h2 h3 => by simp [h1, h2, h3], trivial, trivial, trivial⟩
  · simp only [ite_true, show Reg.rdi ≠ Reg.rsi by decide, show Reg.rdi ≠ Reg.r15 by decide,
      show Reg.rsi ≠ Reg.r15 by decide, ite_false]
    bv_omega
  · simp only [ite_true, sb, lastKey, show Reg.rsi ≠ Reg.r15 by decide, ite_false,
      show Reg.r9 ≠ Reg.rsi by decide, show Reg.r9 ≠ Reg.rdi by decide, show Reg.r9 ≠ Reg.r15 by decide]
    rfl

theorem keyDone_ok (s : State) :
    ∃ s', runBlock isa (keyDone ++ ([.alu .test .r8 (.reg .r8)] : List Instr)) s = some s' ∧
      s'.gpr .rdi = s.gpr .rsi + 64 ∧ s'.zf = some (s.gpr .r8 == 0) ∧
      (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [keyDone, movR, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some, Option.map_some]; rfl, ?_⟩
  simp only [State.setReg, arithFlags, State.setFlags]
  refine ⟨?_, by simp, fun r h => by simp [h], trivial, trivial, trivial⟩
  simp only [ite_true, show (64 : BitVec 32).signExtend 64 = 64 by decide]

/-! ## The whole function -/

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A frame within the writable regions. -/
theorem frame_wr {rs : List Region} {m m' : Mem} {C D b : Addr} {len : Nat} (hf : Frame rs m m')
    (h : ∀ r ∈ rs, Region.Sub r ⟨C, 16⟩ ∨ Region.Sub r ⟨D, len⟩ ∨ Region.Sub r ⟨b, 2048⟩) :
    Frame [⟨C, 16⟩, ⟨D, len⟩, ⟨b, 2048⟩] m m' :=
  hf.sub fun r hr => by
    rcases h r hr with h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

theorem saved_frame {s₀ : State} {b : Addr} {m m' : Mem} {rs : List Region} (h : Saved s₀ b m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 384, 48⟩ r) :
    Saved s₀ b m' := fun i hi => by
  rw [← h i hi]
  exact hf.readW (off_contains b (by omega_arith) (by omega_arith) (by omega_arith)) hd (by decide)

theorem notKeyWrites : ∀ r ∈ [Reg.rdx, .r8, .r9, .rsp], r ∉ keyWrites := by decide

/-- The output: the data in place, `r11` out of place. -/
def dOut (to : Bool) (s : State) : Addr := if to then s.gpr .r11 else s.gpr .rcx

/-- What both contracts give: the source (`rcx`) and the output (`dOut`), the
same in place, disjoint out of place, and the other buffers. -/
structure CPre (to : Bool) (s₀ : State) : Prop where
  hwC : (⟨s₀.gpr .rdx, 16⟩ : Region) ∈ s₀.wr
  hwD : (⟨dOut to s₀, 16 * (s₀.gpr .r8).toNat⟩ : Region) ∈ s₀.wr
  hwS : (⟨s₀.gpr .r9, 2048⟩ : Region) ∈ s₀.wr
  hrS : (⟨s₀.gpr .rdi, 240⟩ : Region) ∈ s₀.rd
  hsrc : (⟨s₀.gpr .rcx, 16 * (s₀.gpr .r8).toNat⟩ : Region) ∈ s₀.rd ++ s₀.wr
  dSC : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .rdx, 16⟩
  dSS : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .r9, 2048⟩
  dCS : Region.Disjoint ⟨s₀.gpr .rdx, 16⟩ ⟨s₀.gpr .r9, 2048⟩
  dCD : Region.Disjoint ⟨s₀.gpr .rdx, 16⟩ ⟨dOut to s₀, 16 * (s₀.gpr .r8).toNat⟩
  dCX : Region.Disjoint ⟨s₀.gpr .rdx, 16⟩ ⟨s₀.gpr .rcx, 16 * (s₀.gpr .r8).toNat⟩
  dDS : Region.Disjoint ⟨dOut to s₀, 16 * (s₀.gpr .r8).toNat⟩ ⟨s₀.gpr .r9, 2048⟩
  dXS : Region.Disjoint ⟨s₀.gpr .rcx, 16 * (s₀.gpr .r8).toNat⟩ ⟨s₀.gpr .r9, 2048⟩
  dRC : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨s₀.gpr .rdx, 16⟩
  dRD : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨dOut to s₀, 16 * (s₀.gpr .r8).toNat⟩
  dRS : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨s₀.gpr .r9, 2048⟩
  mode : Mode to (s₀.gpr .rcx) (dOut to s₀) (s₀.gpr .r8).toNat
  hR : (s₀.gpr .rsi).toNat = 10 ∨ (s₀.gpr .rsi).toNat = 12 ∨ (s₀.gpr .rsi).toNat = 14

/-- `16 n` bytes disjoint from a 16-byte region fit in the address space. -/
theorem n16_of_disj {C X : Addr} {n : Nat} (h : Region.Disjoint ⟨C, 16⟩ ⟨X, 16 * n⟩) : 16 * n < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hc => h C (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (C - X).isLt
  omega_arith

theorem CPre.of {s₀ : State} (hp : Proof.Aes.ctr32X86_64.pre s₀) : CPre false s₀ := by
  obtain ⟨hrd, hwr, dSC, dSD, dSS, dCD, dCS, dDS, dRC, dRD, dRS, -, hR⟩ := hp
  exact { hwC := by rw [hwr]; simp, hwD := by rw [hwr]; simp [dOut], hwS := by rw [hwr]; simp,
          hrS := by rw [hrd]; simp, hsrc := by rw [hwr]; simp, dSC, dSS, dCS, dCD, dCX := dCD, dDS,
          dXS := dDS, dRC, dRD, dRS, mode := .inl ⟨rfl, rfl⟩, hR }

theorem CPre.ofTo {s₀ : State} (hp : AesNi.ctr32ToX86_64.pre s₀) : CPre true s₀ := by
  obtain ⟨hrd, hwr, dSC, dSD, dSS, dCX, dCD, dCS, dXD, dXS, dDS, dRC, dRD, dRS, -, -, hR⟩ := hp
  exact { hwC := by rw [hwr]; simp, hwD := by rw [hwr]; simp [dOut], hwS := by rw [hwr]; simp,
          hrS := by rw [hrd]; simp, hsrc := by rw [hrd]; simp, dSC, dSS, dCS, dCD, dCX, dDS, dXS, dRC, dRD,
          dRS, mode := .inr ⟨rfl, dXD⟩, hR }

theorem CPre.n16 {to : Bool} {s₀ : State} (hp : CPre to s₀) : 16 * (s₀.gpr .r8).toNat < 2 ^ 64 :=
  n16_of_disj hp.dCD

/-- What the code ensures, in place or out of place. -/
def CPost (to : Bool) (s₀ s' : State) : Prop :=
  Spec.Gcm.blocksAt s'.mem (dOut to s₀) (s₀.gpr .r8).toNat =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith (s₀.gpr .rsi).toNat
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (16 * ((s₀.gpr .rsi).toNat + 1))))
        (Spec.Gcm.blockAt s₀.mem (s₀.gpr .rdx)) (Spec.Gcm.blocksAt s₀.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat) ∧
    Spec.Gcm.blockAt s'.mem (s₀.gpr .rdx) =
      Nat.repeat Spec.Gcm.inc32 (s₀.gpr .r8).toNat (Spec.Gcm.blockAt s₀.mem (s₀.gpr .rdx))

theorem core (to : Bool) {s₀ : State} (hp : CPre to s₀)
    (hx : to = true → (s₀.xmm .xmm15).extractLsb' 0 64 = s₀.gpr .r11) {Q : State → Prop}
    (hQ : ∀ s', gprPreserved s₀ s' → CPost to s₀ s' → Q s') :
    WP isa (.block saveRegs) s₀ fun a => WP isa (.block ctrSetup) a fun b => WP isa (.block keySetup) b fun c =>
      WP isa (.seq (.loop (.block keyBody) .ae)
        (.seq (.block (dstInit to ++ Sse.srSetup ++ keyDone ++ ([.alu .test .r8 (.reg .r8)] : List Instr)))
          (.seq (.ite .e (.block []) (.loop (Sse.groupG to) .ne)) (.block restoreRegs)))) c Q := by
  have hwC := hp.hwC
  have hwD := hp.hwD
  have hwS := hp.hwS
  have hrS := hp.hrS
  have dSC := hp.dSC
  have dSS := hp.dSS
  have dCS := hp.dCS
  have dCD := hp.dCD
  have dCX := hp.dCX
  have dDS := hp.dDS
  have dXS := hp.dXS
  have hR := hp.hR
  have n16 := hp.n16
  have hR14 : (s₀.gpr .rsi).toNat ≤ 14 := by omega_arith
  -- The prologue.
  obtain ⟨s₁, h₁, sv₁, g₁, rd₁, wr₁, f₁⟩ := save_ok hwS rfl (by decide)
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  obtain ⟨s₂, h₂, m₂, rdx₂, o₂, rd₂, wr₂⟩ :=
    ctrSetup_ok (s := s₁) (b := s₀.gpr .r9) (ctr := s₀.gpr .rdx) (by rw [g₁]; rfl) (by rw [g₁])
      (wr₁ ▸ hwS) (wr₁ ▸ hwC)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain ⟨s₃, h₃, r15₃, rdi₃, rsi₃, o₃, m₃, rd₃, wr₃⟩ := keySetup_ok s₂
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  have x₃ : s₃.xmm = s₀.xmm := ((xmm_block (by decide) h₃).trans (xmm_block (by decide) h₂)).trans
    (xmm_block (by decide) h₁)
  -- Registers and memory after the prologue.
  have g₃ : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r15 → r ≠ .rdi → r ≠ .rsi → s₃.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₃ r h3 h4 h5, o₂ r h1 h2, g₁]
  have hb₃ : s₃.gpr sb = s₀.gpr .r9 := g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have fS : Frame [⟨s₀.gpr .r9 + BitVec.ofNat 64 (8 * 54), 20⟩, ⟨s₀.gpr .rdx, 16⟩] s₁.mem s₃.mem := by
    rw [m₃, m₂, g₁]; exact setup_frame dCS
  have f₀₃ : Frame [⟨s₀.gpr .r9, 2048⟩, ⟨s₀.gpr .rdx, 16⟩] s₀.mem s₃.mem := by
    refine (f₁.sub fun r hr => ⟨⟨s₀.gpr .r9, 2048⟩, by simp, ?_⟩).trans
      (fS.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s₀.gpr .r9, 2048⟩, by simp, scr_sub _ (by omega_arith)⟩
      · exact ⟨⟨s₀.gpr .rdx, 16⟩, by simp, sub_refl _⟩
  let R := (s₀.gpr .rsi).toNat
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (16 * (R + 1))
  have hk : KSetup s₃ (s₀.gpr .r9) (s₀.gpr .rdi) R w :=
    { scr := by rw [wr₃, wr₂, wr₁]; exact hwS
      base := hb₃
      sch := List.mem_append_left _ (by rw [rd₃, rd₂, rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₃.bytes (R := ⟨s₀.gpr .rdi, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega_arith)).symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dSS
        · exact dSC }
  have hi₃ : KInv s₃ (s₀.gpr .r9) (s₀.gpr .rdi) R w R s₃ :=
    { hj := Nat.le_refl _
      r15 := by rw [r15₃, o₂ _ (by decide) (by decide), g₁]; simp [R]
      rdi := by rw [rdi₃, o₂ _ (by decide) (by decide), o₂ _ (by decide) (by decide), g₁]
      rsi := by rw [rsi₃, o₂ _ (by decide) (by decide), g₁]; simp [keyAddr, sb]
      rd := rfl
      wr := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_arith) }
  -- The key loop, which writes no SSE register.
  have hkv : keyBody.all (fun i => !KeepReg.writesVec i) = true := by lit_decide
  refine WP.seq (WP.mono (WP.xkeep rfl (by simpa [Code.all] using hkv) (keyLoop_ok hk hi₃)) fun s₄ ⟨d₄, x₄⟩ => ?_)
  refine WP.seq ?_
  -- The output pointer's slot, ShiftRows' masks, then the round keys' address.
  rw [List.append_assoc (dstInit to ++ Sse.srSetup), WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  have hb₄ : s₄.gpr .r9 = s₀.gpr .r9 := by rw [d₄.keep .r9 (by decide)]; exact hb₃
  have hw₄ : (⟨s₀.gpr .r9, 2048⟩ : Region) ∈ s₄.wr := by rw [d₄.wr, wr₃, wr₂, wr₁]; exact hwS
  refine dstInit_wp to (s := s₄) (b := s₀.gpr .r9) hb₄ hw₄ fun s₄ᵢ sl₄ o₄ᵢ f₄ᵢ _ rd₄ᵢ wr₄ᵢ => ?_
  obtain ⟨s₄', h₄', mk₄, fm₄, g₄', rd₄', wr₄'⟩ :=
    Sse.srSetup_ok (s := s₄ᵢ) (b := s₀.gpr .r9) ((o₄ᵢ .r9 (by decide)).trans hb₄) (wr₄ᵢ ▸ hw₄)
  refine WP.of_runBlock ⟨s₄', h₄', ?_⟩
  obtain ⟨s₅, h₅, rdi₅, z₅, o₅, m₅, rd₅, wr₅⟩ := keyDone_ok s₄'
  refine WP.of_runBlock ⟨s₅, h₅, ?_⟩
  have g₅ : ∀ r ∈ [Reg.rdx, .r8, .r9, .rsp], s₅.gpr r = s₃.gpr r := fun r hr => by
    rw [o₅ r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      g₄' r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      o₄ᵢ r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      d₄.keep r (notKeyWrites r hr)]
  have r8₅ : s₅.gpr .r8 = s₀.gpr .r8 := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hb₅ : s₅.gpr sb = s₀.gpr .r9 := by rw [show sb = .r9 from rfl, g₅ _ (by simp)]; exact hb₃
  have hK0 : s₅.gpr .rdi = s₀.gpr .r9 + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [rdi₅, g₄' .rsi (by decide), o₄ᵢ .rsi (by decide), d₄.rsi]
    simp only [keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
  have hRR : R ≤ 14 := hR14
  have fK : Frame [⟨s₀.gpr .r9 + BitVec.ofNat 64 0, 384⟩, ⟨s₀.gpr .r9 + BitVec.ofNat 64 1024, 1024⟩,
      ⟨s₀.gpr .r9 + BitVec.ofNat 64 464, 32⟩, dRegion (s₀.gpr .r9)] s₃.mem s₅.mem := by
    refine ((d₄.frame.mono fun r hr => ?_).trans (f₄ᵢ.mono fun r hr => ?_)).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
    · simp only [List.mem_singleton] at hr; subst hr; simp
    · rw [m₅]; exact fm₄.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [Sse.srOff]
  have kd : ∀ {x lx}, 384 ≤ x → x + lx ≤ 456 → ∀ r ∈ [(⟨s₀.gpr .r9 + BitVec.ofNat 64 0, 384⟩ : Region),
      ⟨s₀.gpr .r9 + BitVec.ofNat 64 1024, 1024⟩, ⟨s₀.gpr .r9 + BitVec.ofNat 64 464, 32⟩, dRegion (s₀.gpr .r9)],
      Region.Disjoint ⟨s₀.gpr .r9 + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h1 h2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by simp only [dSlot]; omega_arith) (by omega_arith) (by simp only [dSlot]; omega_arith)
  have cd : ∀ {x lx}, x + lx ≤ 16 → ∀ r ∈ [(⟨s₀.gpr .r9, 8 * 54⟩ : Region)],
      Region.Disjoint ⟨s₀.gpr .rdx + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (dCS.sub_right (Region.sub_prefix (by omega_arith))).sub_left (Offset.sub_base _ h)
  obtain ⟨sl₁, sl₂, sl₃⟩ := setup_slots (m := s₁.mem) (N := s₁.gpr .r8) dCS
  rw [← m₂, ← m₃] at sl₁ sl₂ sl₃
  have clo₅ : cloW s₅.mem (s₀.gpr .r9) = s₀.mem.readW (s₀.gpr .rdx) 64 := by
    rw [cloW, fK.readW (Region.contains_self _ _) (kd (by omega_arith) (by omega_arith)) (by decide), ← cloW, sl₁,
      f₁.readW (Region.contains_self _ _) (cd (by omega_arith)) (by decide)]
    simp
  have chi₅ : chiW s₅.mem (s₀.gpr .r9) = (s₀.mem.readW (s₀.gpr .rdx + BitVec.ofNat 64 8) 32).setWidth 64 := by
    rw [chiW, fK.readW (Region.contains_self _ _) (kd (by omega_arith) (by omega_arith)) (by decide), ← chiW, sl₂,
      f₁.readW (Region.contains_self _ _) (cd (by omega_arith)) (by decide)]
  have num₅ : numW s₅.mem (s₀.gpr .r9) = bswap32 (s₀.mem.readW (s₀.gpr .rdx + BitVec.ofNat 64 12) 32) := by
    rw [numW, fK.readW (Region.contains_self _ _) (kd (by omega_arith) (by omega_arith)) (by decide), ← numW, sl₃,
      f₁.readW (Region.contains_self _ _) (cd (by omega_arith)) (by decide)]
  let icb := Spec.Gcm.blockAt s₀.mem (s₀.gpr .rdx)
  let n := (s₀.gpr .r8).toNat
  have hs : GSetup to s₅ (s₀.gpr .r9) (s₀.gpr .rcx) (dOut to s₀) n R w icb :=
    { scr := by rw [wr₅, wr₄', wr₄ᵢ, d₄.wr, wr₃, wr₂, wr₁]; exact hwS
      dat := by rw [wr₅, wr₄', wr₄ᵢ, d₄.wr, wr₃, wr₂, wr₁]; exact hwD
      src := by rw [rd₅, wr₅, rd₄', wr₄', rd₄ᵢ, wr₄ᵢ, d₄.rd, d₄.wr, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.hsrc
      hn := n16
      mode := hp.mode
      sep := dDS
      ssep := dXS
      rounds := hR
      keys := fun j hj => keyRel_congr (d₄.keys j hj) fun k hk => by
        rw [m₅, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 1920 - 64 * R + 64 * j =
          1920 - 64 * (R - j) by omega_arith]
        refine (fm₄.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans
          (f₄ᵢ.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide))
        · simp only [List.mem_singleton] at hr; subst hr
          rw [wordAddr, VG.Offset.add_add]
          exact Offset.disjoint _ (by simp [Sse.srOff]; omega_arith) (by omega_arith) (by simp [Sse.srOff])
        · simp only [List.mem_singleton] at hr; subst hr
          rw [wordAddr, VG.Offset.add_add]
          exact Offset.disjoint _ (by simp only [dSlot]; omega_arith) (by omega_arith)
            (by simp only [dSlot]; omega_arith)
      lo := fun i hi j hj => by
        rw [clo₅, readW_bit _ _ hi hj, blockAt_bit _ _ (by omega_arith) hj]
      hi := fun i hi j hj => by
        rw [chi₅, BitVec.getLsbD_setWidth, show 8 * (7 - i) + j = 8 * (15 - (8 + i)) + j by omega_arith,
          blockAt_bit _ _ (by omega_arith) hj, BitVec.ofNat_add, ← BitVec.add_assoc,
          Mem.readW_byte s₀.mem (s₀.gpr .rdx + BitVec.ofNat 64 8) hi, BitVec.getLsbD_extractLsb']
        simp [hj, show 8 * i + j < 64 by omega_arith]
      hi' := fun p hp => by
        rw [chi₅, BitVec.getLsbD_setWidth]
        simp [BitVec.getLsbD_of_ge _ _ hp] }
  -- The data is as on entry.
  have dd : ∀ r ∈ [(⟨s₀.gpr .r9, 2048⟩ : Region), ⟨s₀.gpr .rdx, 16⟩],
      Region.Disjoint ⟨dOut to s₀, 16 * n⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dDS
    · exact dCD.symm
  have ds : ∀ r ∈ [(⟨s₀.gpr .r9, 2048⟩ : Region), ⟨s₀.gpr .rdx, 16⟩],
      Region.Disjoint ⟨s₀.gpr .rcx, 16 * n⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dXS
    · exact dCX.symm
  have kfr : ∀ X : Addr, Region.Disjoint ⟨X, 16 * n⟩ ⟨s₀.gpr .r9, 2048⟩ → ∀ r ∈ [(⟨s₀.gpr .r9 + BitVec.ofNat 64 0, 384⟩ : Region),
      ⟨s₀.gpr .r9 + BitVec.ofNat 64 1024, 1024⟩, ⟨s₀.gpr .r9 + BitVec.ofNat 64 464, 32⟩, dRegion (s₀.gpr .r9)],
      Region.Disjoint ⟨X, 16 * n⟩ r := by
    intro X hX r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hX.sub_right (scr_sub _ (by (try simp only [dSlot]); omega_arith))
  have data₅ : DataInv s₀.mem s₅.mem (s₀.gpr .rcx) (dOut to s₀) n 0 (keyStream R w icb) :=
    dataInv_frame fK (kfr _ dDS) n16 (dataInv_frame f₀₃ dd n16 fun i hi => by simp)
  have src₅ : SrcInv s₀.mem s₅.mem (s₀.gpr .rcx) n 0 :=
    srcInv_frame fK (kfr _ dXS) n16 (srcInv_frame f₀₃ ds n16 fun i hi _ => rfl)
  have slot₅ : to = true → s₅.mem.readW (dAddr (s₀.gpr .r9)) 64 = dOut to s₀ + BitVec.ofNat 64 (64 * 0) := by
    intro ht
    subst ht
    rw [m₅, fm₄.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by simp only [dSlot, Sse.srOff]; omega_arith) (by simp only [dSlot]; omega_arith)
          (by simp only [Sse.srOff]; omega_arith)) (by decide),
      sl₄ rfl, x₄, x₃, hx rfl]
    simp [dOut]
  refine WP.seq (WP.mono (Q := GDone s₀.mem s₅ (s₀.gpr .r9) (s₀.gpr .rcx) (dOut to s₀) n R w icb) ?_
    fun s₆ gd => ?_)
  · have r8₄ : s₄'.gpr .r8 = s₀.gpr .r8 := by rw [← o₅ .r8 (by decide)]; exact r8₅
    refine WP.ite (s₀.gpr .r8 == 0) (by simp [X86_64.eval, z₅, r8₄]) (fun h0 => ?_) (fun h0 => ?_)
    · exact WP.block_nil ⟨hb₅, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by
        simp only [beq_iff_eq] at h0; simp [n, h0] at hi⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      refine Sse.groups_ok hs (by rw [m₅]; exact mk₄)
        ⟨by omega_arith, ?_, slot₅, ?_, hb₅, hK0, rfl, rfl, rfl, Frame.refl _ _, ?_, data₅, src₅⟩
      · rw [g₅ _ (by simp), o₃ _ (by decide) (by decide) (by decide), rdx₂, g₁]; simp
      · rw [r8₅]; simp [n]
      · rw [num₅, icb_lo]; simp [icb]
  -- The epilogue.
  have sv : Saved s₀ (s₀.gpr .r9) s₆.mem := by
    refine saved_frame (saved_frame (saved_frame sv₁ fS ?_) fK ?_) gd.frame ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact (dCS.sub_right (scr_sub _ (by omega_arith))).symm
    · exact kd (by omega_arith) (by omega_arith)
    · intro r hr
      simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (scr_disj _ (by omega_arith) (by omega_arith)).symm
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (by simp only [dSlot]; omega_arith) (by omega_arith) (by simp only [dSlot]; omega_arith)
      · exact (dDS.sub_right (scr_sub _ (by omega_arith))).symm
  obtain ⟨s₇, h₇, rg₇, o₇, fR⟩ :=
    restore_ok (by rw [gd.wr, wr₅, wr₄', wr₄ᵢ, d₄.wr, wr₃, wr₂, wr₁]; exact hwS) gd.base (by decide) sv
  refine WP.of_runBlock ⟨s₇, h₇, ?_⟩
  have fsub : ∀ {x lx}, x + lx ≤ 2048 → Region.Sub ⟨s₀.gpr .r9 + BitVec.ofNat 64 x, lx⟩ ⟨s₀.gpr .r9, 2048⟩ :=
    fun h => scr_sub _ h
  have fG : Frame [⟨s₀.gpr .rdx, 16⟩, ⟨dOut to s₀, 16 * n⟩, ⟨s₀.gpr .r9, 2048⟩] s₀.mem s₇.mem := by
    refine (((frame_wr f₀₃ ?_).trans (frame_wr fK ?_)).trans (frame_wr gd.frame ?_)).trans (frame_wr fR ?_)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (sub_refl _))
      · exact .inl (sub_refl _)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact .inr (.inr (fsub (by (try simp only [dSlot]); omega_arith)))
    · intro r hr
      simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inr (.inr (Region.sub_prefix (by omega_arith)))
      · exact .inr (.inr (fsub (by omega_arith)))
      · exact .inr (.inr (fsub (by simp only [dSlot]; omega_arith)))
      · exact .inr (.inl (sub_refl _))
    · intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (Region.sub_prefix (by omega_arith)))
  have rsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := by
    rw [o₇ _ (fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_arith) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide), gd.rsp, rsp₅]
  refine hQ _ ⟨fun r hr => ?_, ?_⟩ ⟨?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₇ 0 (by omega_arith)
    · exact rg₇ 1 (by omega_arith)
    · exact rsp₇
    · exact rg₇ 2 (by omega_arith)
    · exact rg₇ 3 (by omega_arith)
    · exact rg₇ 4 (by omega_arith)
    · exact rg₇ 5 (by omega_arith)
  · refine fG.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dRC
    · exact hp.dRD
    · exact hp.dRS
  · exact ctr32_of_dataInv (dataInv_frame fR (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dDS.sub_right (Region.sub_prefix (by omega_arith))) n16 gd.data)
  · refine ctr_after fun k hk => ?_
    have hC : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨s₀.gpr .rdx, 16⟩ r) →
        m' (s₀.gpr .rdx + BitVec.ofNat 64 k) = m (s₀.gpr .rdx + BitVec.ofNat 64 k) :=
      fun hf hd => hf.bytes hd (by simp) hk
    rw [hC fR (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dCS.sub_right (Region.sub_prefix (by omega_arith))),
      hC gd.frame (fun r hr => by
        simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact dCS.sub_right (Region.sub_prefix (by omega_arith))
        · exact dCS.sub_right (fsub (by omega_arith))
        · exact dCS.sub_right (fsub (by simp only [dSlot]; omega_arith))
        · exact dCD),
      hC fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact dCS.sub_right (fsub (by (try simp only [dSlot]); omega_arith))),
      m₃, m₂, setup_ctr dCS hk, g₁,
      f₁.readW (Region.contains_self _ _) (cd (by omega_arith)) (by decide)]
    split
    · exact hC f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dCS.sub_right (Region.sub_prefix (by omega_arith))
    · simp

theorem correct (to : Bool) {s₀ : State} (hp : CPre to s₀) :
    WP isa (Impl.Aes.X86_64.ctr32G to) s₀ fun s' => gprPreserved s₀ s' ∧ CPost to s₀ s' := by
  unfold Impl.Aes.X86_64.ctr32G
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  refine dstStash_wp to fun sₛ hxₛ gₛ mₛ rdₛ wrₛ => ?_
  have hpₛ : CPre to sₛ := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hp
    simp only [dOut] at *
    rw [← gₛ, ← rdₛ, ← wrₛ] at *
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩
  refine core to hpₛ (fun ht => by rw [hxₛ ht, gₛ]) fun s' h1 h2 => ⟨?_, ?_⟩
  · simp only [gprPreserved, gₛ, mₛ] at h1; exact h1
  · simp only [CPost, dOut, gₛ, mₛ] at h2 ⊢; exact h2

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32X86_64.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.ctr32 s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct false (CPre.of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem ctr32To_correct (s : State) (hs : AesNi.ctr32ToX86_64.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.ctr32To s t s' ∧ abiPreserved s s' ∧ AesNi.ctr32ToX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct true (CPre.ofTo hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32X86_64.pre Proof.Aes.ctr32X86_64.pub
    Impl.Aes.X86_64.ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The taint analysis of `vg_aes_ctr32_to` starts knowing the lengths of the
writable regions and that `r9` is the scratch buffer, whose output-pointer
slot the code keeps public. -/
def τTo : VG.X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r11], flags := false, lens := [16, 0, 2048],
    bases := [(.r9, 2, 0)] }

theorem τTo_wf {s : State} (h : AesNi.ctr32ToX86_64.pre s) : VG.X86_64.Taint.Wf τTo s := by
  obtain ⟨-, hwr, -, -, -, -, dCD, dCS, -, -, dDS, -, -, -, -, hwD, -⟩ := h
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
  · rw [hwr]; simp [τTo]
  · rw [hwr]
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨dCD, dCS⟩, dDS, fun _ h => h.elim⟩
  · rw [hwr]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  · simp only [τTo, List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp
    simp [VG.X86_64.Taint.region, hwr]

theorem ctr32To_ct : ConstantTime isa AesNi.ctr32ToX86_64.pre AesNi.ctr32ToX86_64.pub Impl.Aes.X86_64.ctr32To := by
  refine VG.Taint.constantTime (A := taint) τTo ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨p1, p2, p3, p4, p5, p6, p7⟩
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, τTo_wf h₁, τTo_wf h₂, ?_, ?_, ?_,
    VG.X86_64.Taint.noXr⟩
  · simp only [τTo, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p3, p5, p6, p7]
  · intro sl h; simp [τTo] at h
  · intro sl h; simp [τTo] at h
  · intro r hr; simp [τTo] at hr

end VG.Proof.Aes.X86_64
