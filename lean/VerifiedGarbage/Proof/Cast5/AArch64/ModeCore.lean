module

public import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
public import VerifiedGarbage.Proof.Cast5.ModeCipher
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import VerifiedGarbage.Impl.Cast5.AArch64.Modes
public import VerifiedGarbage.Proof.Cast5.AArch64.Block
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Proof.Cast5.AArch64.Ecb
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Copy
import VerifiedGarbage.Proof.Modes.AArch64.Counter
import VerifiedGarbage.Proof.Modes.AArch64.Unchain
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Proof.Modes.AArch64.Core
public import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.AesCtr.Ctr32
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
public import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
public import VerifiedGarbage.Proof.Modes.AArch64.Copy
public import VerifiedGarbage.Proof.Modes.AArch64.Counter
public import VerifiedGarbage.Proof.Modes.AArch64.Steps
public import VerifiedGarbage.Proof.Modes.AArch64.Unchain
public import VerifiedGarbage.Proof.Modes.AArch64.Words
public import VerifiedGarbage.Proof.Modes.Addr
public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Ctr.Contract

/-!
# CAST5's core for the modes on AArch64

`dirCoreSpec up`: CAST5's core (`Impl.Cast5.AArch64.dirCore up`) meets what
the modes need of a core of one-word blocks (`Proof.Modes.AArch64.BlockSpec`),
with the key the subkeys and the number of rounds, its cipher encryption
(`up`) or decryption (`Proof.Cast5.dirCipher`), and the key ready (`Ready`)
when the subkeys are at `x0`, readable and outside every writable region
(`SchedAt`), `x1` holds the number of rounds, and the table of S-boxes is
where the static `VG_CAST5_S1234` puts it, readable and apart from every
writable region (`TabAt`): nothing the modes or the core write can reach
either. `crypt` is ECB's block code (`encryptBlock_ok`, `decryptBlock_ok`)
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
  rw [hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega)]

theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} (h : Held m T s1234) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 4096⟩ r) : Held m' T s1234 := by
  intro i hi
  rw [s1234_length] at hi
  rw [← h i (by rw [s1234_length]; exact hi)]
  exact hf.readW (r := ⟨T, 4096⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

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
@[simp] theorem dirCore_bw (up : Bool) : (dirCore up).bw = 1 := rfl

theorem core_eq (up : Bool) (B : Addr) : coreRegion (dirCore up) B = ⟨B, 8⟩ := rfl
theorem total_eq (up : Bool) : (dirCore up).total = 13 := rfl

theorem x0_not_mode (up : Bool) : Reg.x0 ∉ Modes.AArch64.modeRegs (dirCore up) := by
  simp only [Modes.AArch64.modeRegs, dirCore]; decide

theorem x1_not_mode (up : Bool) : Reg.x1 ∉ Modes.AArch64.modeRegs (dirCore up) := by
  simp only [Modes.AArch64.modeRegs, dirCore]; decide

theorem ready_frame {up : Bool} {s s' : State} {kn : Spec.Cast5.Schedule × Nat} {rs : List Region}
    (h : Ready s kn) (hf : Frame rs s.mem s'.mem) (hw : WrIn rs s s')
    (hg : ∀ r, r ∉ Modes.AArch64.modeRegs (dirCore up) → s'.gpr r = s.gpr r) : Ready s' kn := by
  obtain ⟨⟨p, hp, hk, hS⟩, h1, hn, hT⟩ := h
  refine ⟨⟨p, by rw [hg _ (x0_not_mode up), hp], ?_, hS.congr hw.rd hw.wr⟩, by rw [hg _ (x1_not_mode up), h1],
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

theorem prepare_wp {up : Bool} {s : State} {B : Addr} {rs : List Region} {kn : Spec.Cast5.Schedule × Nat}
    (hB : s.gpr sb = B) (_ : ScrIn s B (dirCore up).total) (_ : (⟨B, 8 * (dirCore up).total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs kn) :
    WP isa (dirCore up).prepare s fun s' => Ready s' kn ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
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

theorem block_ok (up : Bool) {u : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre u k n) :
    WP isa (if up then encryptBlock else decryptBlock) u
      (BPost u (dirBlock up k n (Spec.Cast5.blockAt u.mem (u.gpr .x2)))) := by
  cases up
  · exact decryptBlock_ok h
  · exact encryptBlock_ok h

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

theorem crypt_wp {up : Bool} {s : State} {B : Addr} {kn : Spec.Cast5.Schedule × Nat} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore up).total) (hr : Ready s kn) :
    WP isa (dirCore up).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ Ready s' kn ∧
      Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧
      (∀ j < (dirCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up) B j) (8 * (dirCore up).bw) =
        dirCipher up kn.1 kn.2 (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up) B j) (8 * (dirCore up).bw))) ∧
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
      exact ⟨_, hw, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  show WP isa (cryptCode up) s _
  refine WP.seq (WP.of_runBlock ⟨u, eu, ?_⟩)
  refine WP.seq (WP.mono (block_ok up hpre) fun v ⟨vout, vf, _, _, vrd, vwr, vsy, vg⟩ => ?_)
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
  · have hj0 : j = 0 := by simp only [dirCore, Impl.Modes.AArch64.Core.G] at hj; omega
    subst hj0
    have ea : blkAddr (dirCore up) B 0 = B := by simp [dirCore]
    rw [dirCore_bw, ea, Nat.mul_one, dirCipher_bytes, bytesAt_eq, m', vout, um]

/-- CAST5's core, encrypting (`up`) or decrypting, meets what the modes need. -/
def dirCoreSpec (up : Bool) : BlockSpec (dirCore up) where
  Key := Spec.Cast5.Schedule × Nat
  cipher kn := dirCipher up kn.1 kn.2
  KeyArgs := ModeKeyArgs
  Ready s _ kn := Ready s kn
  cipher_len kn b := by rw [dirCore_bw]; exact dirCipher_length up kn.1 kn.2 b
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
theorem crypt_keeps : KeepsReg .x25 (dirCore true).prepare ∧ KeepsReg .x25 (dirCore true).crypt := by
  refine ⟨keepsReg_of_regSafe (by decide), keepsReg_of_regSafe ?_⟩
  show regSafe .x25 (cryptCode true) = true
  lit_decide

end VG.Proof.Cast5.AArch64.Mode
