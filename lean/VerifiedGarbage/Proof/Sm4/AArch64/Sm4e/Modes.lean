module

public import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
public import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
public import VerifiedGarbage.Proof.Modes.AArch64.Core
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
public import VerifiedGarbage.Proof.Sm4.CbcScratch
public import VerifiedGarbage.Proof.Sm4.FbScratch
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Proof.Sm4.Contract
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.Ctr32
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
import VerifiedGarbage.Proof.Modes.AArch64.CfbDec.Whole
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Modes
meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
meta import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Modes.AArch64.Core
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Sm4.FbScratch
meta import VerifiedGarbage.Proof.Modes.Ctr32
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Sm4.Cfb
meta import VerifiedGarbage.Spec.Sm4.Cbc
meta import VerifiedGarbage.Spec.Sm4.Ctr
meta import VerifiedGarbage.Proof.Sm4.Contract
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Modes.AArch64.Ctr
meta import VerifiedGarbage.Proof.Modes.AArch64.Ctr32
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CfbDec.Whole
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# SM4's core for the modes with the Armv8 SM4 instructions

`coreSpec d`, `coreSpec1 d`: the cores that transform eight blocks, or one,
with `sm4e` (`Impl.Sm4.AArch64.Sm4e.core d`, `core1 d`) meet what the modes
need of a core
(`Proof.Modes.AArch64.CoreSpec`), with the key a schedule and its cipher
`Spec.Sm4.cipher` for encryption and `Spec.Sm4.invCipher` for decryption
(`dirCipher`, as the bitsliced core's, `ModeCore.lean`).

The core prepares nothing, so the key is ready (`Ready`) when it is where
the caller passed it: the schedule's address in `x0`, which is not one of
the modes' registers, and the schedule readable and apart from every
writable region, so that nothing a mode writes changes it (`ready_frame`).
`KeyArgs` says the same at entry.

`crypt` is ECB's pieces on the buffer (`cryptBuf_wp`, for the eight
registers of the one core or the one of the other): the round keys (`dirKeys_ok`), the blocks loaded
(`ldData_ok`), the rounds (`crypt_ok`) and the blocks stored (`stData_ok`),
which writes the buffer only.

`ctr_verified`, `ctr32_verified`, `cbcDecryptChained_verified` and
`cfbDecrypt_verified`: the modes' CTR, counter mode with `inc₃₂`, CBC
decryption and batched CFB decryption (`Proof/Modes/AArch64/`) over this
core, with the working space of 28 words as an argument, are correct and
constant time, by the taint analysis: the pointers, `n` and the stack
pointer are public, and so is everything the code computes from them, which
it keeps in general-purpose registers. The `_framed` theorems run them with
the working space on the stack, zeroed on return: 224 bytes.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Sm4e

open VG VG.AArch64
open VG.Impl.Sm4.AArch64 (Dir)
open VG.Impl.Sm4.AArch64.Sm4e
open VG.Impl.Aes.AArch64 (sb)
open VG.Spec.Sm4 (Word Block blockAt scheduleAt)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4 (quads ofBlock outBlock DInv)
open VG.Proof.Sm4.AArch64 (dirCipher)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion bufAddr CoreSpec WrIn modeRegs)

/-- The schedule at `x0`, outside the regions `rs` and every writable region. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  Proof.Sm4.AArch64.KeyArgs s rs k ∧ ∀ w ∈ s.wr, Region.Disjoint ⟨s.gpr .x0, 128⟩ w

/-- The key is ready where the caller passed it. -/
def Ready (s : State) (k : Spec.Sm4.Schedule) : Prop := KeyArgs s [] k

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Sm4.Schedule} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k :=
  ⟨Proof.Sm4.AArch64.keyArgs_congr h.1 hr hrd hwr hf, by rw [hwr, hr .x0 List.mem_cons_self]; exact h.2⟩

theorem ready_frame {c : Impl.Modes.AArch64.Core} (h0 : Reg.x0 ∉ modeRegs c) {s s' : State}
    {k : Spec.Sm4.Schedule} {rs : List Region} (h : Ready s k)
    (hf : Frame rs s.mem s'.mem) (hw : WrIn rs s s') (hg : ∀ r, r ∉ modeRegs c → s'.gpr r = s.gpr r) :
    Ready s' k := by
  have h0 : s'.gpr .x0 = s.gpr .x0 := hg .x0 h0
  obtain ⟨⟨p, hp, hk, hin, hfit, -⟩, hdis⟩ := h
  subst hp
  refine ⟨⟨s.gpr .x0, h0, ?_, by rw [hw.rd]; exact hin, hfit, fun _ hr => absurd hr List.not_mem_nil⟩,
    by rw [hw.wr, h0]; exact hdis⟩
  rw [hk]
  refine (Proof.Sm4.scheduleAt_congr fun i hi => hf.bytes (R := ⟨s.gpr .x0, 128⟩) (fun r hr => ?_)
    (by show 128 ≤ 2 ^ 64; omega_arith) hi).symm
  obtain ⟨w, hw', hsub⟩ := hw.sub r hr
  exact (hdis w hw').sub_right hsub

/-- Nothing is prepared: the key is ready where it is. -/
theorem ready_of_keyArgs {s : State} {rs : List Region} {k : Spec.Sm4.Schedule} (hk : KeyArgs s rs k) :
    Ready s k := by
  obtain ⟨⟨p, hp, hk', hin, hfit, -⟩, hdis⟩ := hk
  exact ⟨⟨p, hp, hk', hin, hfit, fun _ hr => absurd hr List.not_mem_nil⟩, hdis⟩

/-- The cipher of `d` on the 16 bytes at `p` is the specification's block
function. -/
theorem dirCipher_blockFn (d : Dir) (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (bytesAt m p 16) = (Proof.Sm4.blockFn k (dirOf d) (blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Sm4.cipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]; rfl
  · rw [dirCipher, Spec.Sm4.invCipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]; rfl

/-- A block of the first `c` transformed is its result. -/
theorem dinv_done {m₀ m : Mem} {D : Addr} {n c : Nat} {F : Nat → Block} (h : DInv m₀ m D n c F) {j : Nat}
    (hc : j < c) (hn : c ≤ n) : blockAt m (D + BitVec.ofNat 64 (16 * j)) = F j := by
  apply Vector.ext; intro t ht
  simp only [blockAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_using [hc, hn, ht]), ite_eq_left (by omega_using [hc, ht]),
    show (16 * j + t) / 16 = j by omega_using [ht], show (16 * j + t) % 16 = t by omega_using [ht]]
  simp [Vector.getD, ht]

theorem total_eq (d : Dir) : (core d).total = 28 := rfl

/-- The blocks of the buffer at `B`, one for each register of `regs`, each
replaced with its cipher: the buffer is within `16 n` writable bytes at `B`,
and nothing else is written, no general-purpose register either. -/
theorem cryptBuf_wp (d : Dir) {regs : List VReg} (hrs : regs = regs8 ∨ regs = [.v0]) {s : State} {B : Addr}
    {k : Spec.Sm4.Schedule} {n : Nat} (hB : s.gpr sb = B) (hfB : B.toNat + 16 * n ≤ 2 ^ 64)
    (hwB : (⟨B, 16 * n⟩ : Region) ∈ s.wr) (hn : regs.length ≤ n) (hr : Ready s k) :
    WP isa (.block (cryptBuf regs d)) s fun s' => s'.gpr = s.gpr ∧ Ready s' k ∧
      Frame [⟨B, 16 * regs.length⟩] s.mem s'.mem ∧
      (∀ j < regs.length, bytesAt s'.mem (B + BitVec.ofNat 64 (16 * j)) 16 =
        dirCipher d k (bytesAt s.mem (B + BitVec.ofNat 64 (16 * j)) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hl : regs.length ≤ 8 := by rcases hrs with rfl | rfl <;> decide
  obtain ⟨⟨p, hp, hk, hin, hfit, -⟩, hdis⟩ := hr
  subst hp
  have hbr := bregs_ok regs hrs
  rw [cryptBuf, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  -- The round keys.
  refine WP.mono (dirKeys_ok d (s₀ := s) fun o ho =>
    ⟨_, List.mem_append_left _ hin, Offset.contains_base _ ho (by omega_using [ho])⟩)
    fun s₁ ⟨hK, g₁, m₁, rd₁, wr₁⟩ => ?_
  -- The blocks.
  refine WP.mono (ldData_ok sb regs 0 s₁ hbr.1 (by omega_using [hl]) fun j hj => by
    rw [rd₁, wr₁, g₁, hB]
    exact ⟨_, List.mem_append_right _ hwB, Offset.contains_base _ (by omega_using [hj, hn])
      (by omega_using [hj, hn, hfB])⟩)
    fun s₂ ⟨e₂, f₂⟩ => ?_
  have hK₂ : KeysOk (keyOf s d) s₂ := hK.of_v fun r => f₂.v _ (hbr.2 r)
  refine WP.mono (crypt_ok hbr hK₂) fun s₃ ⟨e₃, f₃⟩ => ?_
  have g₃ : s₃.gpr = s.gpr := by rw [f₃.gpr, f₂.gpr, g₁]
  have m₃ : s₃.mem = s.mem := by rw [f₃.mem, f₂.mem, m₁]
  let F : Nat → Block := fun j =>
    outBlock (quads .enc (keyOf s d) 8 (ofBlock (blockAt s.mem (B + BitVec.ofNat 64 (16 * j)))))
  have hF : ∀ j (h : j < regs.length), ∀ t < 16, vbyte (s₃.v regs[j]) t = (F (0 + 0 + j)).getD t 0 := by
    intro j h t ht
    rw [e₃ _ (List.getElem_mem h) (ofBlock (blockAt s.mem (B + BitVec.ofNat 64 (16 * (0 + 0 + j))))) (by
      rw [e₂ j h, rev32b_readW, g₁, hB, m₁, show 0 + 0 + j = 0 + j by omega_using []])]
    exact vbyte_out _ ht
  refine WP.mono (stData_ok sb (m₀ := s.mem) (D := B) (n := n) (c := 0) (F := F) (by omega_using [hfB]) regs 0 s₃
    (by rw [g₃, hB]; simp) (by omega_using [hl]) (by omega_using [hn])
    (by rw [f₃.wr, f₂.wr, wr₁]; exact hwB)
    (fun i _ => by rw [m₃, ite_eq_right (by omega_using [])]) hF)
    fun s₄ ⟨d₄, g₄, _, _, rd₄, wr₄, fr₄⟩ => ?_
  have g : s₄.gpr = s.gpr := by rw [g₄, g₃]
  have rd : s₄.rd = s.rd := by rw [rd₄, f₃.rd, f₂.rd, rd₁]
  have wr : s₄.wr = s.wr := by rw [wr₄, f₃.wr, f₂.wr, wr₁]
  have hfr : Frame [⟨B, 16 * regs.length⟩] s.mem s₄.mem := by
    intro x hx
    have hx' : ¬ (x - B).toNat + 1 ≤ 16 * regs.length := hx _ List.mem_cons_self
    by_cases hxn : (x - B).toNat < 16 * n
    · have e : x = B + BitVec.ofNat 64 (x - B).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      rw [e, d₄ _ hxn, ite_eq_right (by omega_using [hx'])]
    · rw [fr₄ x hxn, m₃]
  refine ⟨g, ?_, hfr, fun j hj => ?_, rd, wr⟩
  · refine ⟨⟨s.gpr .x0, by rw [g], ?_, by rw [rd]; exact hin, hfit, fun _ hr => absurd hr List.not_mem_nil⟩,
      by rw [wr, g]; exact hdis⟩
    rw [hk]
    exact (Proof.Sm4.scheduleAt_congr fun i hi => hfr.bytes (R := ⟨s.gpr .x0, 128⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hdis _ hwB).sub_right (Region.sub_prefix (by omega_using [hn])))
      (by show 128 ≤ 2 ^ 64; omega_arith) hi).symm
  · rw [dirCipher_blockFn, Proof.Sm4.bytesAt_eq_blockAt, blockFn_eq, hk,
      dinv_done d₄ (show j < 0 + 0 + regs.length by omega_using [hj]) (by omega_using [hn])]

/-- The cores: of the eight blocks in `regs8`, or of the one in `v0`. -/
def CoreOk (regs : List VReg) (lg : Nat) : Prop := (regs = regs8 ∧ lg = 3) ∨ (regs = [.v0] ∧ lg = 0)

theorem crypt_wp (d : Dir) {regs : List VReg} {lg : Nat} (hc : CoreOk regs lg) {s : State} {B : Addr}
    {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B) (hs : ScrIn s B (coreOf regs lg d).total) (hr : Ready s k) :
    WP isa (coreOf regs lg d).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ Ready s' k ∧
      Frame [coreRegion (coreOf regs lg d) B] s.mem s'.mem ∧
      (∀ j < (coreOf regs lg d).G, bytesAt s'.mem (bufAddr (coreOf regs lg d) B j) 16 =
        dirCipher d k (bytesAt s.mem (bufAddr (coreOf regs lg d) B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hG : (coreOf regs lg d).G = regs.length := by rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have e : 16 * (regs.length + 6) = 8 * (coreOf regs lg d).total := by
    show _ = 8 * (2 * regs.length + 12); omega_using []
  have e' : 16 * regs.length = 8 * (coreOf regs lg d).slots := by
    show _ = 8 * (2 * regs.length); omega_using []
  refine WP.mono (cryptBuf_wp d (hc.imp And.left And.left) (n := regs.length + 6) hB (by rw [e]; exact hs.fit)
    (by rw [e]; exact hs.wr) (Nat.le_add_right _ _) hr) fun s' ⟨g, r, f, c, rd, wr⟩ =>
    ⟨by rw [g, hB], by rw [g], by rw [g], r, by rw [e'] at f; exact f, fun j hj => ?_, rd, wr⟩
  have ha : bufAddr (coreOf regs lg d) B j = B + BitVec.ofNat 64 (16 * j) :=
    congrArg (B + BitVec.ofNat 64 ·) (show 8 * 0 + 16 * j = 16 * j by omega_using [])
  rw [ha]
  exact c j (hG ▸ hj)

/-- The core's blocks are two words. -/
@[simp] theorem core_bw (d : Dir) : (core d).bw = 2 := rfl
@[simp] theorem core1_bw (d : Dir) : (core1 d).bw = 2 := rfl

/-- A core with `sm4e` meets what the modes need, for the direction `d`. -/
def coreSpecOf (d : Dir) {regs : List VReg} {lg : Nat} (hc : CoreOk regs lg) : CoreSpec (coreOf regs lg d) where
  Key := Spec.Sm4.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready s _ k := Ready s k
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher]
  layout := by
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases d <;>
      exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  keyRegs_ok := by rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases d <;> decide
  regs_ok := by rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases d <;> decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf _ hw hg :=
    ready_frame (by rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases d <;> decide) h hf hw hg
  prepare_wp hB _ _ hk := WP.block_nil ⟨ready_of_keyArgs hk, hB, rfl, rfl, Frame.refl _ _, rfl, rfl⟩
  crypt_wp := crypt_wp d hc

/-- The core of eight blocks. -/
def coreSpec (d : Dir) : CoreSpec (core d) := coreSpecOf d (.inl ⟨rfl, rfl⟩)

/-- The core of one block. -/
def coreSpec1 (d : Dir) : CoreSpec (core1 d) := coreSpecOf d (.inr ⟨rfl, rfl⟩)

/-! ## The modes -/

/-- The precondition of the modes on AArch64, with the data `len` bytes
long and the working space of `w` words at `x4`. -/
def mPre (w : Nat) (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .x0, 128⟩
  let iv : Region := ⟨s.gpr .x1, 16⟩
  let data : Region := ⟨s.gpr .x2, len s⟩
  let scratch : Region := ⟨s.gpr .x4, 8 * w⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * w ≤ 2 ^ 64

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 16 * (s.gpr .x3).toNat

/-- The public arguments. -/
def mPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev schedOf (s : State) : Spec.Sm4.Schedule := scheduleAt s.mem (s.gpr .x0)
abbrev ivOf (s : State) : List Byte := bytesAt s.mem (s.gpr .x1) 16
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.Cbc.blocksAt m (s.gpr .x2) (s.gpr .x3).toNat

/-- CTR with its working space at `x4`. -/
def ctrC : Contract isa where
  pre := mPre 28 blkLen
  post s s' := blocksOf s s'.mem = Spec.Ctr.crypt (Spec.Sm4.cipher (schedOf s)) (ivOf s) (blocksOf s s.mem) ∧
    bytesAt s'.mem (s.gpr .x1) 16 = Spec.Ctr.next (ivOf s) (s.gpr .x3).toNat
  pub := mPub

/-- Counter mode with `inc₃₂`, with its working space at `x4`. -/
def ctr32C : Contract isa where
  pre := mPre 28 blkLen
  post s s' :=
    Spec.Gcm.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
        Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher (schedOf s)) (Spec.Gcm.blockAt s.mem (s.gpr .x1))
          (Spec.Gcm.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
      Spec.Gcm.blockAt s'.mem (s.gpr .x1) =
        Nat.repeat Spec.Gcm.inc32 (s.gpr .x3).toNat (Spec.Gcm.blockAt s.mem (s.gpr .x1))
  pub := mPub

/-- CBC decryption that updates the chaining value. -/
def cbcDecC : Contract isa where
  pre := mPre 28 blkLen
  post s s' := blocksOf s s'.mem = Spec.Cbc.decrypt (Spec.Sm4.invCipher (schedOf s)) (ivOf s) (blocksOf s s.mem) ∧
    bytesAt s'.mem (s.gpr .x1) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := mPub

/-- CFB128 decryption. -/
def cfbDecC : Contract isa where
  pre := mPre 28 blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (Spec.Sm4.cipher (schedOf s)) (ivOf s) (blocksOf s s.mem) ∧
    bytesAt s'.mem (s.gpr .x1) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := mPub

attribute [local irreducible] Spec.Sm4.cipher in
/-- The core's cipher is the contracts', without unfolding it. -/
theorem cipher_eq (k : Spec.Sm4.Schedule) : (coreSpec .encrypt).cipher k = Spec.Sm4.cipher k := rfl

attribute [local irreducible] Spec.Sm4.cipher in
theorem gcmCipher_eq (k : Spec.Sm4.Schedule) :
    Proof.Modes.onBlocks ((coreSpec .encrypt).cipher k) = Spec.Sm4.gcmCipher k := rfl

attribute [local irreducible] Spec.Sm4.cipher in
theorem batchCipher_eq (k : Spec.Sm4.Schedule) : ((coreSpec .encrypt).toBlock rfl).cipher k = Spec.Sm4.cipher k :=
  rfl

attribute [local irreducible] Spec.Sm4.invCipher in
theorem invCipher_eq (k : Spec.Sm4.Schedule) :
    ((coreSpec .decrypt).toBlock rfl).cipher k = Spec.Sm4.invCipher k := rfl

/-- The key arguments of the precondition, outside any writable regions `rs`. -/
theorem keyArgs_of_pre' {w : Nat} {len : State → Nat} {s : State} (hp : mPre w len s) (rs : List Region)
    (hrs : ∀ r ∈ rs, r ∈ s.wr) : KeyArgs s rs (schedOf s) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, -, -, -, fitK, -⟩ := hp
  have hdis : ∀ r ∈ s.wr, Region.Disjoint ⟨s.gpr .x0, 128⟩ r := fun r hr => by
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dKV
    · exact dKD
    · exact dKS
  exact ⟨⟨s.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => hdis r (hrs r hr)⟩, hdis⟩

/-- The key arguments of the precondition. -/
theorem keyArgs_of_pre {w : Nat} {len : State → Nat} {s : State} (hp : mPre w len s) :
    KeyArgs s [⟨s.gpr .x4, 8 * w⟩, ⟨s.gpr .x1, 16⟩] (schedOf s) :=
  keyArgs_of_pre' hp _ fun r hr => by
    rw [hp.2.1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl
    · exact .inr (.inr rfl)
    · exact .inl rfl

/-- What each mode keeps of the callee-saved registers. -/
abbrev Saved (s₀ s' : State) : Prop :=
  ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
    s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)

theorem ctr_wp {s₀ : State} (hp : ctrC.pre s₀) : WP isa ctr s₀ fun s' => Saved s₀ s' ∧ ctrC.post s₀ s' := by
  have hk := keyArgs_of_pre hp
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, fitK, fitC, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.ctr_wp (coreSpec .encrypt) (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := schedOf s₀) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dCS dDS dCD fitD hk) fun s' ⟨hcs, hdata, hctr, _, _, _⟩ =>
      ⟨hcs, ?_, hctr⟩
  rw [cipher_eq] at hdata
  exact hdata

theorem ctr32_wp {s₀ : State} (hp : ctr32C.pre s₀) :
    WP isa ctr32 s₀ fun s' => Saved s₀ s' ∧ ctr32C.post s₀ s' := by
  have hk := keyArgs_of_pre hp
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, fitK, fitC, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.ctr32_wp (coreSpec .encrypt) (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := schedOf s₀) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dCS dDS dCD fitD hk) fun s' ⟨hcs, hdata, hctr, _, _, _⟩ =>
      ⟨hcs, ?_, hctr⟩
  rw [gcmCipher_eq] at hdata
  exact hdata

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecC.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => Saved s₀ s' ∧ cbcDecC.post s₀ s' := by
  have hk := keyArgs_of_pre hp
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecryptChained_wp ((coreSpec .decrypt).toBlock rfl)
    (r := ⟨.x1, .x2, .x3, .x4⟩) ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := schedOf s₀) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD hk) fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [invCipher_eq] at hdata
  exact ⟨hdata, hiv⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecC.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => Saved s₀ s' ∧ cfbDecC.post s₀ s' := by
  have hk := keyArgs_of_pre hp
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Modes.AArch64.CfbDec.batched_wp ((coreSpec .encrypt).toBlock rfl)
    (r := ⟨.x1, .x2, .x3, .x4⟩) ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := schedOf s₀) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD hk) fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [batchCipher_eq] at hdata
  exact ⟨hdata, hiv⟩

/-! ## The contracts -/

/-- Correct, from a mode's `WP`: the code has no calls and writes neither
`x30` nor the low halves of `v8`–`v15`. -/
theorem correct_of {c : Prog isa} {k : Contract isa}
    (hw : ∀ s, k.pre s → WP isa c s fun s' => Saved s s' ∧ k.post s s')
    (h30 : c.allInstrs (fun i => [Reg.x30].all fun r => !clobbers i r) = true) (hn : c.noCalls = true)
    (hv : c.allInstrs keepsV = true) (s : State) (hs : k.pre s) :
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (hw s hs) h30 hn
  exact ⟨t, s', he, ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he hv⟩, h₂⟩

theorem taint_agree {w : Nat} {len : State → Nat} (s₁ s₂ : State) (_ : mPre w len s₁) (_ : mPre w len s₂)
    (hp : mPub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block). -/
def mSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 28⟩]

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV or counter block at `0x2000`, one block at `0x3000`. -/
def frameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩]

theorem ctr_verified : Verified AArch64.target ctr (Proof.Sm4.ctrScratchContract AArch64.abi 28) :=
  Verified.of_correct (correct_of (k := ctrC) (fun _ => ctr_wp) (by lit_decide) (by lit_decide) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) taint_agree (by taint_decide))
    (by
      sig_implies [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Proof.Sm4.ctrPost, ctrC, mPre, mPub,
        AArch64.abi, AArch64.argRegs] [mSat] using mSat)

theorem ctr32_verified : Verified AArch64.target ctr32 (Proof.Sm4.ctr32ScratchContract AArch64.abi 28) :=
  Verified.of_correct (correct_of (k := ctr32C) (fun _ => ctr32_wp) (by lit_decide) (by lit_decide) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) taint_agree (by taint_decide))
    (by
      sig_implies [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Post, ctr32C, mPre,
        mPub, AArch64.abi, AArch64.argRegs] [mSat] using mSat)

theorem cbcDecryptChained_verified :
    Verified AArch64.target cbcDecryptChained (Proof.Sm4.cbcDecChainedScratchContract AArch64.abi 28) :=
  Verified.of_correct
    (correct_of (k := cbcDecC) (fun _ => cbcDecryptChained_wp) (by lit_decide) (by lit_decide) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) taint_agree (by taint_decide))
    (by
      sig_implies [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
        Proof.Sm4.cbcDecChainedPost, cbcDecC, mPre, mPub, AArch64.abi, AArch64.argRegs] [mSat] using mSat)

theorem cfbDecrypt_verified :
    Verified AArch64.target cfbDecrypt (Proof.Sm4.fbScratchContract AArch64.abi 28 Proof.Sm4.cfbDecPost) :=
  Verified.of_correct
    (correct_of (k := cfbDecC) (fun _ => cfbDecrypt_wp) (by lit_decide) (by lit_decide) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) taint_agree (by taint_decide))
    (by
      sig_implies [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Proof.Sm4.cfbDecPost,
        cfbDecC, mPre, mPub, AArch64.abi, AArch64.argRegs] [mSat] using mSat)

/-! ## The working space on the stack -/

theorem ctrFrameSat_pre : ∃ s, (Spec.Sm4.ctrContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, AArch64.abi, AArch64.argRegs] [frameSat] using frameSat

theorem ctr32FrameSat_pre : ∃ s, (Proof.Sm4.ctr32Contract AArch64.abi 224).pre s := by
  implies_sat [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, AArch64.abi, AArch64.argRegs] [frameSat] using frameSat

theorem cbcDecFrameSat_pre : ∃ s, (Spec.Sm4.cbcDecryptChainedContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Sm4.cbcDecryptChainedContract, Spec.Sm4.cbcChainedSig, AArch64.abi, AArch64.argRegs]
    [frameSat] using frameSat

theorem cfbDecFrameSat_pre : ∃ s, (Spec.Sm4.cfbDecryptContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Sm4.cfbDecryptContract, Spec.Sm4.cfbSig, Spec.Sm4.ofbSig, AArch64.abi, AArch64.argRegs]
    [frameSat] using frameSat

/-- `vg_sm4_ctr_sm4`: CTR with its working space on the stack, which the
function as emitted zeroes (`Impl.Scrub.AArch64.scrubAll`). -/
theorem ctr_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 224 .x4 ctr)
      (Spec.Sm4.ctrContract AArch64.abi 224) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.ctrSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Sm4.ctrPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) ctr_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Sm4.ctrPostOut_local _ vs m m₁ m₂ r hl hb h) ctrFrameSat_pre

/-- `vg_sm4_ctr32_sm4`: counter mode with `inc₃₂`, with its working space on
the stack. -/
theorem ctr32_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 ctr32)
      (Proof.Sm4.ctr32Contract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Proof.Sm4.ctr32Sig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Sm4.ctr32Post AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) ctr32_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.ctr32PostOut_local _) ctr32FrameSat_pre

/-- `vg_sm4_cbc_decrypt_chained_sm4`: CBC decryption with its working space
on the stack. -/
theorem cbcDecryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 cbcDecryptChained)
      (Spec.Sm4.cbcDecryptChainedContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Sm4.cbcDecChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cbcDecryptChained_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.cbcDecChainedPostOut_local _) cbcDecFrameSat_pre

/-- `vg_sm4_cfb128_decrypt_sm4`: CFB128 decryption with its working space on
the stack. -/
theorem cfbDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 cfbDecrypt)
      (Spec.Sm4.cfbDecryptContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cfbSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Sm4.cfbDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cfbDecrypt_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.cfbDecPostOut_local _) cfbDecFrameSat_pre

end VG.Proof.Sm4.AArch64.Sm4e
