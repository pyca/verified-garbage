module

public import VerifiedGarbage.Proof.Cast5.Rounds
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Proof.Cast5.ModeScratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
meta import VerifiedGarbage.Proof.Modes.AArch64.Fb
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Cast5.AArch64.Block
public import VerifiedGarbage.Impl.Cast5.Tables
meta import VerifiedGarbage.Proof.Cast5.AArch64.Block
meta import VerifiedGarbage.Impl.Cast5.Tables
public import VerifiedGarbage.Proof.Cast5.ModeCipher
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import VerifiedGarbage.Impl.Cast5.AArch64.Modes
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Cast5.ModeCipher
meta import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
meta import VerifiedGarbage.Impl.Cast5.AArch64.Modes
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps

/-! ### `Cast5.AArch64.ModeCore`, which this module and modules that import it used -/

section

/-!
# CAST5's core for the modes on AArch64

`dirCoreSpec`: CAST5's encrypting core (`Impl.Cast5.AArch64.dirCore`) meets
what the modes need of a core of one-word blocks
(`Proof.Modes.AArch64.BlockSpec`), with the key the subkeys and the number of
rounds, its cipher encryption, and the key ready (`Ready`)
when the subkeys are at `x0`, readable and outside every writable region
(`SchedAt`), `x1` holds the number of rounds, and the table of S-boxes is
where the static `VG_CAST5_S1234` puts it, readable and apart from every
writable region (`TabAt`): nothing the modes or the core write can reach
either. `crypt` is the block code (`encryptBlock_ok`)
on the buffer, between its own setup and finish. `crypt_keeps`: the core
keeps `x25`, where the feedback modes keep the IV's address.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Mode

open VG VG.AArch64 VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (s1234Sym s1234)
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Proof.Cast5 (Held dirCipher dirCipher_length bytesAt_eq ofFn_bytesAt)
open VG.Proof.Modes.AArch64 (ScrIn WrIn coreRegion blkRegion blkAddr BlockSpec movR_ok runBlock_app
  runBlock_syms KeepsReg regSafe keepsReg_of_regSafe)

/-! ## Memory -/

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) : Spec.Cast5.scheduleAt m' p = Spec.Cast5.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Cast5.scheduleAt, Vector.getElem_ofFn]
  have hb := fun j (hj : j < 128) => hf.bytes (R := ⟨p, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) hj
  rw [hb _ (by omega_using [hi]), hb _ (by omega_using [hi]), hb _ (by omega_using [hi]), hb _ (by omega_using [hi])]

theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} (h : Held m T s1234) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 4096⟩ r) : Held m' T s1234 := by
  intro i hi
  rw [s1234_length] at hi
  rw [← h i (by rw [s1234_length]; exact hi)]
  exact hf.readW (r := ⟨T, 4096⟩) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hd (by decide)

/-! ## The key -/

/-- The table of S-boxes at the static's address: readable, within the
address space, holding the S-boxes, and apart from every writable region. -/
structure TabAt (s : State) : Prop where
  rd : (⟨s.syms s1234Sym, 4096⟩ : Region) ∈ s.rd
  fit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64
  held : Held s.mem (s.syms s1234Sym) s1234
  sep : ∀ w ∈ s.wr, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ w

/-- `TabAt` survives what keeps the regions and the statics and writes memory
apart from the table. -/
theorem TabAt.frame {s s' : State} (h : TabAt s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r) : TabAt s' := by
  refine ⟨?_, ?_, ?_, fun w hw => ?_⟩
  · rw [hrd, hsy]; exact h.rd
  · rw [hsy]; exact h.fit
  · rw [hsy]; exact held_frame h.held hf hd
  · rw [hwr] at hw; rw [hsy]; exact h.sep w hw

/-- The subkeys at `p`: readable, within the address space, and outside every
writable region. -/
structure SchedAt (s : State) (p : Addr) : Prop where
  rd : (⟨p, 128⟩ : Region) ∈ s.rd
  fit : p.toNat + 128 ≤ 2 ^ 64
  sep : ∀ w ∈ s.wr, Region.Disjoint ⟨p, 128⟩ w

theorem SchedAt.congr {s s' : State} {p : Addr} (h : SchedAt s p) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    SchedAt s' p :=
  ⟨by rw [hrd]; exact h.rd, h.fit, by rw [hwr]; exact h.sep⟩

/-- The subkeys at `x0` and the number of rounds in `x1`; the subkeys and the
table outside the regions `rs`. -/
def ModeKeyArgs (s : State) (rs : List Region) (kn : Spec.Cast5.Schedule × Nat) : Prop :=
  (∃ p : Addr, s.gpr .x0 = p ∧ kn.1 = Spec.Cast5.scheduleAt s.mem p ∧ SchedAt s p ∧
    ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) ∧
  s.gpr .x1 = BitVec.ofNat 64 kn.2 ∧ (kn.2 = 12 ∨ kn.2 = 16) ∧ TabAt s ∧
  ∀ r ∈ rs, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r

/-- The key `kn` is ready: its subkeys at `x0`, its number of rounds in `x1`,
and the table. -/
def Ready (s : State) (kn : Spec.Cast5.Schedule × Nat) : Prop :=
  (∃ p : Addr, s.gpr .x0 = p ∧ Spec.Cast5.scheduleAt s.mem p = kn.1 ∧ SchedAt s p) ∧
    s.gpr .x1 = BitVec.ofNat 64 kn.2 ∧ (kn.2 = 12 ∨ kn.2 = 16) ∧ TabAt s

/-- The core's blocks are one word. -/
@[simp] theorem dirCore_bw : dirCore.bw = 1 := rfl

theorem core_eq (B : Addr) : coreRegion dirCore B = ⟨B, 8⟩ := rfl
theorem total_eq : dirCore.total = 13 := rfl

theorem x0_not_mode : Reg.x0 ∉ Modes.AArch64.modeRegs dirCore := by
  simp only [Modes.AArch64.modeRegs, dirCore]; decide

theorem x1_not_mode : Reg.x1 ∉ Modes.AArch64.modeRegs dirCore := by
  simp only [Modes.AArch64.modeRegs, dirCore]; decide

theorem ready_frame {s s' : State} {kn : Spec.Cast5.Schedule × Nat} {rs : List Region}
    (h : Ready s kn) (hf : Frame rs s.mem s'.mem) (hw : WrIn rs s s')
    (hg : ∀ r, r ∉ Modes.AArch64.modeRegs dirCore → s'.gpr r = s.gpr r) : Ready s' kn := by
  obtain ⟨⟨p, hp, hk, hS⟩, h1, hn, hT⟩ := h
  refine ⟨⟨p, by rw [hg _ x0_not_mode, hp], ?_, hS.congr hw.rd hw.wr⟩, by rw [hg _ x1_not_mode, h1],
    hn, hT.frame hw.rd hw.wr hw.syms hf fun r hr => ?_⟩
  · rw [scheduleAt_frame hf fun r hr => ?_, hk]
    obtain ⟨w, hw', hsub⟩ := hw.sub r hr
    exact (hS.sep w hw').sub_right hsub
  · obtain ⟨w, hw', hsub⟩ := hw.sub r hr
    exact (hT.sep w hw').sub_right hsub

theorem keyArgs_congr {s s' : State} {rs : List Region} {kn : Spec.Cast5.Schedule × Nat}
    (h : ModeKeyArgs s rs kn) (hr : ∀ r ∈ [Reg.x0, .x1], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs kn := by
  obtain ⟨⟨p, hp, hk, hS, hdis⟩, h1, hn, hT, hdT⟩ := h
  refine ⟨⟨p, by rw [hr .x0 (by simp), hp], ?_, hS.congr hrd hwr, hdis⟩,
    by rw [hr .x1 (by simp), h1], hn, hT.frame hrd hwr hsy hf hdT, by rw [hsy]; exact hdT⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {kn : Spec.Cast5.Schedule × Nat}
    (hB : s.gpr sb = B) (_ : ScrIn s B dirCore.total) (_ : (⟨B, 8 * dirCore.total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs kn) :
    WP isa dirCore.prepare s fun s' => Ready s' kn ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion dirCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨⟨p, hp, hk, hS, -⟩, h1, hn, hT, -⟩ := hk
  exact WP.block_nil ⟨⟨⟨p, hp, hk.symm, hS⟩, h1, hn, hT⟩, hB, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## `crypt` -/

/-- The block's encryption (`up`) or decryption. -/
def dirBlock (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (b : Spec.Cast5.Block) : Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n b else Spec.Cast5.decryptBlock k n b

theorem dirCipher_bytes (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (m : Mem) (p : Addr) :
    dirCipher up k n (Spec.Aes.bytesAt m p 8) = (dirBlock up k n (Spec.Cast5.blockAt m p)).toList := by
  cases up <;> simp only [dirCipher, dirBlock, Spec.Cast5.cipher, Spec.Cast5.invCipher, ofFn_bytesAt,
    Bool.false_eq_true, ite_true, ite_false]

/-- What `modeSetup` does. -/
theorem setup_run (s : State) :
    ∃ u, runBlock isa modeSetup s = some u ∧ u.gpr .x16 = s.gpr sb ∧ u.gpr .x2 = s.gpr sb ∧
      (∀ x, x ≠ .x16 → x ≠ .x2 → u.gpr x = s.gpr x) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .x16 sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .x2 sb
  refine ⟨s₂, ?_, by rw [o₂ _ (by decide), r₁], by rw [r₂, o₁ _ (by decide)],
    fun x h1 h2 => by rw [o₂ x h2, o₁ x h1], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  show runBlock isa ([movR .x16 sb] ++ ([movR .x2 sb] : List Instr)) s = some s₂
  rw [runBlock_app, e₁, Option.bind_some, e₂]

theorem crypt_wp {s : State} {B : Addr} {kn : Spec.Cast5.Schedule × Nat} (hB : s.gpr sb = B)
    (hs : ScrIn s B dirCore.total) (hr : Ready s kn) :
    WP isa dirCore.crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ Ready s' kn ∧
      Frame [coreRegion dirCore B] s.mem s'.mem ∧
      (∀ j < dirCore.G, Spec.Aes.bytesAt s'.mem (blkAddr dirCore B j) (8 * dirCore.bw) =
        dirCipher true kn.1 kn.2 (Spec.Aes.bytesAt s.mem (blkAddr dirCore B j) (8 * dirCore.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨k, n⟩ := kn
  obtain ⟨⟨p, hp, hK, hS⟩, h1, hn, hT⟩ := hr
  have hw := hs.wr
  have hfB := hs.fit
  rw [total_eq] at hw hfB
  -- The buffer: the scratch buffer's first word, apart from the subkeys and the table.
  have sBuf : Region.Sub ⟨B, 8⟩ ⟨B, 8 * 13⟩ := Region.sub_prefix (by decide)
  have dKB : Region.Disjoint ⟨p, 128⟩ ⟨B, 8⟩ := (hS.sep _ hw).sub_right sBuf
  have dTB : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨B, 8⟩ := (hT.sep _ hw).sub_right sBuf
  -- The setup.
  obtain ⟨u, eu, u16, u2, ug, um, urd, uwr⟩ := setup_run s
  have usy : u.syms = s.syms := runBlock_syms eu
  have hpre : BPre u k n := by
    refine ⟨⟨?_, fun j hj => ?_, ?_, ?_⟩, hn, by rw [ug _ (by decide) (by decide), h1], ?_⟩
    · rw [ug _ (by decide) (by decide), hp, urd, uwr]
      exact ⟨_, List.mem_append_left _ hS.rd, Region.contains_self _ _⟩
    · rw [ug _ (by decide) (by decide), hp, um, ← scheduleAt_getD _ _ hj, hK]
    · unfold Readable; rw [urd, uwr, usy]
      exact ⟨_, List.mem_append_left _ hT.rd, Region.contains_self _ _⟩
    · rw [um, usy]; exact hT.held
    · rw [u2, hB, uwr]
      exact ⟨_, hw, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []⟩
  show WP isa (cryptCode) s _
  refine WP.seq (WP.of_runBlock ⟨u, eu, ?_⟩)
  refine WP.seq (WP.mono (encryptBlock_ok hpre) fun v ⟨vout, vf, _, _, vrd, vwr, vsy, vg⟩ => ?_)
  rw [u2, hB] at vf vout
  obtain ⟨s', es, r', o', m', rd', wr'⟩ := movR_ok v sb .x16
  refine WP.of_runBlock ⟨s', es, ?_⟩
  have sy' : s'.syms = s.syms := by rw [runBlock_syms es, vsy, usy]
  have hk : ∀ x, x ∉ blockRegs → x ≠ .x2 → x ≠ .x3 → x ≠ .x16 → x ≠ sb → s'.gpr x = s.gpr x :=
    fun x h0 h2 h3 h16 hsb => by rw [o' x hsb, vg x h0 h2 h3, ug x h16 h2]
  have fr : Frame [⟨B, 8⟩] s.mem s'.mem := by rw [m', ← um]; exact vf
  have rdE : s'.rd = s.rd := by rw [rd', vrd, urd]
  have wrE : s'.wr = s.wr := by rw [wr', vwr, uwr]
  refine ⟨by rw [r', vg _ (by decide) (by decide) (by decide), u16, hB],
    hk _ (by decide) (by decide) (by decide) (by decide) (by decide),
    hk _ (by decide) (by decide) (by decide) (by decide) (by decide),
    ⟨⟨p, by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide), hp], ?_, hS.congr rdE wrE⟩,
      by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide), h1], hn,
      hT.frame rdE wrE sy' fr fun r hr => ?_⟩, by rw [core_eq]; exact fr, fun j hj => ?_, rdE, wrE⟩
  · rw [scheduleAt_frame fr fun r hr => ?_]
    · exact hK
    simp only [List.mem_singleton] at hr; subst hr; exact dKB
  · simp only [List.mem_singleton] at hr; subst hr; exact dTB
  · have hj0 : j = 0 := by simp only [dirCore, Impl.Modes.AArch64.Core.G] at hj; omega_using [hj]
    subst hj0
    have ea : blkAddr dirCore B 0 = B := by simp [dirCore]
    rw [dirCore_bw, ea, Nat.mul_one, dirCipher_bytes, bytesAt_eq, m', vout, um]
    rfl

/-- CAST5's encrypting core meets what the modes need. -/
def dirCoreSpec : BlockSpec dirCore where
  Key := Spec.Cast5.Schedule × Nat
  cipher kn := dirCipher true kn.1 kn.2
  KeyArgs := ModeKeyArgs
  Ready s _ kn := Ready s kn
  cipher_len kn b := by rw [dirCore_bw]; exact dirCipher_length true kn.1 kn.2 b
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, Impl.Modes.AArch64.Core.G]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore]; decide, by simp only [dirCore]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.AArch64.regsOk]; decide
  keyArgs_congr h hr hrd hwr hsy hf := keyArgs_congr h hr hrd hwr hsy hf
  ready_frame h hf _ hw hg := ready_frame h hf hw hg
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

/-- The core keeps `x25`, where the feedback modes keep the IV's address. -/
theorem crypt_keeps : KeepsReg .x25 dirCore.prepare ∧ KeepsReg .x25 dirCore.crypt := by
  refine ⟨keepsReg_of_regSafe (by decide), keepsReg_of_regSafe ?_⟩
  show regSafe .x25 (cryptCode) = true
  lit_decide

end VG.Proof.Cast5.AArch64.Mode

end

end

/-! ### `Cast5.AArch64.TableSat`, which this module and modules that import it used -/

section

/-!
# CAST5 on AArch64: the table of the scans, for the contracts' witnesses

The modes whose block code scans `VG_CAST5_S1234` state their contracts on
`AArch64.abi.withConsts ecbConsts`; their witnesses hold the table at
`0x100000` (`ecbSatMem`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64
open VG.Impl.Cast5 (s1234 s1234Sym ecbConsts)

theorem ecbConsts_eq : ecbConsts = [(s1234Sym, s1234)] := rfl

/-- The memory of the contracts' witness: the table at `0x100000` (irreducible:
unfolding it in a definitional check would evaluate the table). -/
@[irreducible] def ecbSatMem : Mem := constMem 0x100000 s1234

theorem ecbSatMem_held : ∀ i < 512,
    ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  unfold ecbSatMem
  intro i hi
  exact constMem_held _ _ (by rw [s1234_length]; decide) i (by rw [s1234_length]; exact hi)

end VG.Proof.Cast5.AArch64

end

end

/-!
# CAST5-OFB and -CFB64 encryption on AArch64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`: the modes' OFB and CFB encryption
(`Proof.Modes.AArch64.fb_wp`) over CAST5's core (`Mode.dirCoreSpec`),
with the IV's address in `x25`, which the core never writes
(`Mode.crypt_keeps`), the specification's results (`Proof.Modes.ofb_of`, …),
and the working space at `x5`. The table of S-boxes is readable where the
static `VG_CAST5_S1234` puts it and holds the S-boxes. `ofb_verified`, …:
each is correct and constant time, by the taint analysis: the pointers,
`rounds`, `n`, the stack pointer and the table's address are public, and so
is everything the code computes from them, which it keeps in registers; the
subkeys, the IV and the data are secret. `ofb_framed`, … run them with their
working space on the stack, zeroed on return: 112 bytes, the 13 words of the
scratch buffer and 8 more. CFB64 decryption is in `TblModesVerified.lean`.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Cast5.AArch64.Mode (dirCoreSpec TabAt SchedAt dirCore_bw)

/-- The `n` blocks at `p`, as the modes read them. -/
theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    VG.Proof.Modes.blocksOf 8 m p n = Spec.Cast5.cbcBlocksAt m p n :=
  (Proof.Cast5.cbcBlocksAt_eq m p n).symm

/-- The data, in blocks. -/
abbrev dataOf (s : State) (m : Mem) : List (List Byte) :=
  Spec.Cast5.cbcBlocksAt m (s.gpr .x3) (s.gpr .x4).toNat
/-- The chaining value. -/
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .x2) 8
/-- The subkeys. -/
abbrev keyOf (s : State) : Spec.Cast5.Schedule := Spec.Cast5.scheduleAt s.mem (s.gpr .x0)

/-- The public arguments and the table's address. -/
def cbcPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

/-- The public registers. -/
def modePub : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5]

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) (hv : c.allInstrs keepsV = true) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he hv⟩

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := (s.gpr .x4).toNat * 8

/-- The facts of the feedback modes' precondition on this target, with the
data `len` bytes long and the working space at `x5`. -/
structure FPre (len : State → Nat) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 128⟩, ⟨s.syms s1234Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .x2, 8⟩, ⟨s.gpr .x3, len s⟩, ⟨s.gpr .x5, 104⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s1234Sym + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64
  dTV : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .x2, 8⟩
  dTD : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .x3, len s⟩
  dTS : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .x5, 104⟩
  dKV : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x2, 8⟩
  dKD : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x3, len s⟩
  dKS : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x5, 104⟩
  dVD : Region.Disjoint ⟨s.gpr .x2, 8⟩ ⟨s.gpr .x3, len s⟩
  dVS : Region.Disjoint ⟨s.gpr .x2, 8⟩ ⟨s.gpr .x5, 104⟩
  dDS : Region.Disjoint ⟨s.gpr .x3, len s⟩ ⟨s.gpr .x5, 104⟩
  fK : (s.gpr .x0).toNat + 128 ≤ 2 ^ 64
  fD : (s.gpr .x3).toNat + len s ≤ 2 ^ 64
  fS : (s.gpr .x5).toNat + 104 ≤ 2 ^ 64
  rounds : (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 16

/-- CAST5 encryption under the key of `s`. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Cast5.cipher (keyOf s) (s.gpr .x1).toNat

def ofbX : Contract isa where
  pre := FPre blkLen
  post s s' := dataOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .x4).toNat
  pub := cbcPub

def cfbEncX : Contract isa where
  pre := FPre blkLen
  post s s' := dataOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (dataOf s s.mem))
  pub := cbcPub

/-- The table, as the core needs it. -/
theorem FPre.tabAt {len : State → Nat} {s : State} (h : FPre len s) : TabAt s :=
  ⟨by rw [h.rd]; simp, h.fitT, fun i hi => h.held i (by rw [s1234_length] at hi; exact hi), fun w hw => by
    rw [h.wr] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact h.dTV
    · exact h.dTD
    · exact h.dTS⟩

/-- The subkeys, as the core needs them. -/
theorem FPre.schedAt {len : State → Nat} {s : State} (h : FPre len s) : SchedAt s (s.gpr .x0) :=
  ⟨by rw [h.rd]; simp, h.fK, fun w hw => by
    rw [h.wr] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact h.dKV
    · exact h.dKD
    · exact h.dKS⟩

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the IV
as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : FPre blkLen s₀) :
    WP isa (dirCore.fb mo modeRegs .x25) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat =
        (List.range (s₀.gpr .x4).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .x2) 8 =
        Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat := by
  have hwS : (⟨s₀.gpr .x5, 8 * 13⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have e : 8 * dirCore.bw * (s₀.gpr .x4).toNat = (s₀.gpr .x4).toNat * 8 := by
    rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.AArch64.fb_wp dirCoreSpec mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := (keyOf s₀, (s₀.gpr .x1).toNat)) rfl rfl rfl rfl ⟨hwS, hp.fS⟩
    (by rw [hp.wr]; simp) (by rw [e, hp.wr]; simp) hp.dVS (by rw [e]; exact hp.dDS) (by rw [e]; exact hp.dVD)
    (by rw [e]; exact hp.fD)
    ⟨⟨s₀.gpr .x0, rfl, rfl, hp.schedAt, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dKS⟩,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hp.rounds, hp.tabAt, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dTS⟩ Mode.crypt_keeps)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [dirCore_bw] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem ofb_wp {s₀ : State} (hp : ofbX.pre s₀) :
    WP isa ofb s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ofbX.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
    rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncX.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
      rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _))
      rw [hv, h2, blocksOf_eq]

/-! ## Constant time -/

theorem fbTaint_agree {len : State → Nat} (s₁ s₂ : State) (_ : FPre len s₁) (_ : FPre len s₂)
    (hp : cbcPub s₁ s₂) :
    VG.AArch64.Taint.AgreeS [s1234Sym] (Taint.ofRegs modePub) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩ := hp
  refine ⟨⟨hsp, fun r hr => ?_⟩, fun n hn => ?_⟩
  · simp only [VG.AArch64.Taint.mem_ofRegs, modePub, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4, h5, h6]
  · simp only [List.mem_singleton] at hn
    subst hn
    exact hsy

theorem ofb_ct : ConstantTime isa ofbX.pre ofbX.pub ofb :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) fbTaint_agree (by taint_decide)

theorem cfbEncrypt_ct : ConstantTime isa cfbEncX.pre cfbEncX.pub cfbEncrypt :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) fbTaint_agree (by taint_decide)

/-! ## The contracts -/

/-- OFB's or CFB's contract with the working space as a sixth argument, under
the calling convention with the table (`cfbSig` is `ofbSig`). -/
abbrev fbK (post : Spec.Cast5.ofbSig.Post AArch64.abi.ptrBits) : Contract isa :=
  Proof.Cast5.modeScratchContract (AArch64.abi.withConsts ecbConsts) Spec.Cast5.ofbSig 13
    (Spec.Cast5.ofbPre AArch64.abi.ptrBits) post

/-- A state satisfying the precondition: one block, 16 rounds. -/
def fbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 104⟩]
  syms _ := 0x100000

theorem fb_implies {postX : State → State → Prop} {post : Spec.Cast5.ofbSig.Post AArch64.abi.ptrBits}
    (hpost : ∀ s s', postX s s' → (fbK post).post s s') :
    ({ pre := FPre blkLen, post := postX, pub := cbcPub } : Contract isa).Implies (fbK post) where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
      Spec.Cast5.ofbPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch] at h
    obtain ⟨hdr, hheld, hfit, hdw, -, htk, hw, dKV, dKD, dKS, dVD, dVS, dDS, fK, -, fD, fS, hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), dKV, dKD, dKS,
      dVD, dVS, dDS, fK, fD, fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ hq := hpost s s' hq
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
      AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩
  sat := ⟨fbSat, by
    generalize e : fbSat = s
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
      Spec.Cast5.ofbPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch]
    subst s
    refine ⟨rfl, ecbSatMem_held, by decide, ?_, ?_⟩
    · intro r hr
      change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 8⟩, ⟨0x4000, 104⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · repeat' apply And.intro
      all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem ofb_verified : Verified AArch64.target ofb (fbK (Proof.Cast5.ofbPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ofb_wp hs) (by lit_decide) (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    ofb_ct (fb_implies fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.ofbPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cfbEncrypt_verified :
    Verified AArch64.target cfbEncrypt
      (Proof.Cast5.modeScratchContract (AArch64.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 13
        (Spec.Cast5.cfbPre AArch64.abi.ptrBits) (Proof.Cast5.cfbEncPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbEncrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    cfbEncrypt_ct (fb_implies (post := Proof.Cast5.cfbEncPost AArch64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.cfbEncPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with 112 bytes of stack. -/
def fbFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩]
  syms _ := 0x100000

theorem fbFrame_sat (post : Spec.Cast5.ofbSig.Post AArch64.abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbSig.contract (AArch64.abi.withConsts ecbConsts) (Spec.Cast5.ofbPre AArch64.abi.ptrBits)
      post true (0 + 112)).pre s := by
  refine ⟨fbFrameSat, ?_⟩
  generalize e : fbFrameSat = s
  sig_pre [Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  refine ⟨by decide, rfl, ecbSatMem_held, by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 8⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 ofb)
      (Proof.Cast5.ofbRoundsContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Spec.Cast5.ofbPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.ofbPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    ofb_verified (by decide) (by decide) (by decide) (Proof.Cast5.ofbPostOut_local _) (fbFrame_sat _)

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 cfbEncrypt)
      (Proof.Cast5.cfbEncryptRoundsContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Spec.Cast5.cfbPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cfbEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (Proof.Cast5.cfbEncPostOut_local _) (fbFrame_sat _)

end VG.Proof.Cast5.AArch64
