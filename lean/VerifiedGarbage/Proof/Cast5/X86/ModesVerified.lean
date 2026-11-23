module

public import VerifiedGarbage.Proof.Cast5.Rounds
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Cast5.X86.ModesLit
meta import VerifiedGarbage.Proof.Cast5.X86.ModesLit
public import VerifiedGarbage.Proof.Cast5.ModeScratch
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Modes.X86.CbcChained
meta import VerifiedGarbage.Proof.Modes.X86.CbcChained
public import VerifiedGarbage.Proof.Framework.X86.TaintSym
meta import VerifiedGarbage.Proof.Framework.X86.TaintSym
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Modes.X86.Seq
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.X86.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Modes.StepsChained
meta import VerifiedGarbage.Proof.AesCtr.Inc
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.ReadHalves
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Modes.StepsChained
meta import VerifiedGarbage.Proof.Modes.X86.Counter
meta import VerifiedGarbage.Proof.Modes.X86.Ops
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.Cast5.X86.Modes
public import VerifiedGarbage.Proof.Cast5.ModeCipher
public import VerifiedGarbage.Proof.Cast5.X86.Ecb
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Modes.X86.Core
meta import VerifiedGarbage.Impl.Cast5.X86.Modes
meta import VerifiedGarbage.Proof.Cast5.ModeCipher
meta import VerifiedGarbage.Proof.Cast5.X86.Ecb

/-! ### `Cast5.X86.ModeCore`, which only this module used -/

section

/-!
# CAST5's core for the modes on x86 (32-bit)

`dirCoreSpec up`: CAST5's core (`Impl.Cast5.X86.Modes.dirCore up`) meets what
the modes need of a core (`Proof.Modes.X86.CoreSpec`), with the key the
subkeys and the number of rounds, read through the first two stack
arguments, and its cipher `Spec.Cast5.cipher` or `invCipher`. The key is
ready (`Ready`) while the arguments, the subkeys and the table of S-boxes
are where they were, apart from every writable region and the word below
`esp` (`Base`). `crypt` is ECB's block (`load_ok`, `encryptBlock_ok`,
`decryptBlock_ok`) between its own setup and store (`setup_ok`,
`store_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.Mode

open VG VG.X86 VG.X86.Wp VG.X86.RegUpd VG.Impl.Cast5.X86 VG.Impl.Cast5.X86.Modes
open VG.Impl.Cast5 (s1234Sym s1234)
open VG.Proof.Cast5 (Held dirCipher bytesAt_eq ofFn_bytesAt dirCipher_length)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout ScrIn)

/-- The subkeys at `K`. -/
abbrev keyR (K : BitVec 32) : Region := ⟨K.setWidth 64, 128⟩
/-- The table of S-boxes. -/
abbrev tabR (s : State) : Region := ⟨(s.syms s1234Sym).setWidth 64, 4096⟩
/-- The key's two arguments. -/
abbrev argR (s : State) : Region := ⟨addr (s.gpr .esp) 4, 8⟩
/-- The word below `esp`, which the scans use. -/
abbrev stk (s : State) : Region := below (s.gpr .esp) 4

/-- The key's arguments: the subkeys' address `K` and the number of rounds
`n`; the subkeys `k` at `K` and the table, readable, apart from every
writable region and the word below `esp`. -/
structure Base (s : State) (K : BitVec 32) (k : Spec.Cast5.Schedule) (n : Nat) : Prop where
  fitE : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  sp : 4 ≤ (s.gpr .esp).toNat
  inA : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 8
  argK : s.mem.readW (addr (s.gpr .esp) 4) 32 = K
  argN : s.mem.readW (addr (s.gpr .esp) 8) 32 = BitVec.ofNat 32 n
  nv : n = 12 ∨ n = 16
  fitK : K.toNat + 128 ≤ 2 ^ 32
  inK : InRegions (s.rd ++ s.wr) (K.setWidth 64) 128
  sk : Spec.Cast5.scheduleAt s.mem (K.setWidth 64) = k
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  inT : InRegions (s.rd ++ s.wr) ((s.syms s1234Sym).setWidth 64) 4096
  held : Held s.mem ((s.syms s1234Sym).setWidth 64) s1234
  dW : ∀ r ∈ s.wr, (keyR K).Disjoint r ∧ (tabR s).Disjoint r ∧ (argR s).Disjoint r
  dKs : (keyR K).Disjoint (stk s)
  dTs : (tabR s).Disjoint (stk s)
  dAs : (argR s).Disjoint (stk s)

/-- The second argument's address. -/
theorem addr8 {E : BitVec 32} (h : E.toNat + 12 ≤ 2 ^ 32) : addr E 8 = addr E 4 + BitVec.ofNat 64 4 := by
  rw [addr_eq (by omega_arith), addr_eq (by omega_arith), Offset.add_add]

theorem argR_contains4 (s : State) : (argR s).Contains (addr (s.gpr .esp) 4) (32 / 8) := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith

theorem argR_contains8 {s : State} (h : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32) :
    (argR s).Contains (addr (s.gpr .esp) 8) (32 / 8) := by
  rw [addr8 h]; exact Offset.contains_base _ (by decide) (by decide)

/-- `Base` survives what keeps `esp`, the regions and the statics, and writes
memory apart from the arguments, the subkeys and the table. -/
theorem Base.frame {s s' : State} {K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} {rs : List Region}
    (h : Base s K k n) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (keyR K).Disjoint r ∧ (tabR s).Disjoint r ∧ (argR s).Disjoint r) : Base s' K k n := by
  obtain hA : ∀ r ∈ rs, (argR s).Disjoint r := fun r hr => (hd r hr).2.2
  refine ⟨by rw [hesp]; exact h.fitE, by rw [hesp]; exact h.sp, by rw [hesp, hrd, hwr]; exact h.inA, ?_, ?_, h.nv,
    h.fitK, by rw [hrd, hwr]; exact h.inK, ?_, by rw [hsy]; exact h.fitT, by rw [hsy, hrd, hwr]; exact h.inT, ?_,
    fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [hesp, hf.readW (argR_contains4 s) hA (by decide)]; exact h.argK
  · rw [hesp, hf.readW (argR_contains8 h.fitE) hA (by decide)]; exact h.argN
  · rw [scheduleAt_frame hf fun r hr => (hd r hr).1]; exact h.sk
  · rw [hsy]; exact held_frame h.held hf fun r hr => (hd r hr).2.1
  · rw [hwr] at hr; simp only [tabR, argR, hsy, hesp]; exact h.dW r hr
  · simp only [stk, hesp]; exact h.dKs
  · simp only [tabR, stk, hsy, hesp]; exact h.dTs
  · simp only [argR, stk, hesp]; exact h.dAs

/-- The key's arguments give the key `kn`, apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (kn : Spec.Cast5.Schedule × Nat) : Prop :=
  ∃ K, Base s K kn.1 kn.2 ∧
    ∀ r ∈ rs, (keyR K).Disjoint r ∧ (tabR s).Disjoint r ∧ (argR s).Disjoint r ∧ (stk s).Disjoint r

/-- The key `kn` is ready, with the scratch buffer at `B` apart from the
word below `esp`. -/
def Ready (s : State) (B : BitVec 32) (kn : Spec.Cast5.Schedule × Nat) : Prop :=
  ∃ K, Base s K kn.1 kn.2 ∧ (stk s).Disjoint ⟨B.setWidth 64, 4 * 76⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {kn : Spec.Cast5.Schedule × Nat} (h : KeyArgs s rs kn)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs kn := by
  obtain ⟨K, hb, hd⟩ := h
  refine ⟨K, hb.frame hesp hrd hwr hsy hf fun r hr => ⟨(hd r hr).1, (hd r hr).2.1, (hd r hr).2.2.1⟩,
    fun r hr => ?_⟩
  simp only [tabR, argR, stk, hsy, hesp]
  exact hd r hr

theorem ready_frame {s s' : State} {B : BitVec 32} {kn : Spec.Cast5.Schedule × Nat}
    {rs : List Region} (h : Ready s B kn) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r') : Ready s' B kn := by
  obtain ⟨K, hb, hd⟩ := h
  refine ⟨K, hb.frame hesp hrd hwr hsy hf fun r hr => ?_, by simp only [stk, hesp]; exact hd⟩
  obtain ⟨r', hr', hs⟩ := hsub r hr
  obtain ⟨d1, d2, d3⟩ := hb.dW r' hr'
  exact ⟨d1.sub_right hs, d2.sub_right hs, d3.sub_right hs⟩

theorem dirCore_total (up : Bool) : (dirCore up).total = 76 := rfl

theorem prepare_wp (up : Bool) {s : State} {B : BitVec 32} {rs : List Region} {kn : Spec.Cast5.Schedule × Nat}
    (hB : s.gpr Impl.Modes.X86.sb = B) (_ : ScrIn s B (dirCore up).total)
    (hR : (⟨B.setWidth 64, 4 * (dirCore up).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs kn)
    (_ : (dirCore up).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore up).prepare s fun s' => Ready s' B kn ∧ s'.gpr Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (dirCore up) B, stkRegion (s.gpr .esp) (dirCore up).stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨K, hb, hd⟩ := hk
  exact WP.block_nil ⟨⟨K, hb, (hd _ hR).2.2.2⟩, hB, rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## `crypt` -/

theorem inRegions_prefix {X : List Region} {a : Addr} {n l : Nat} (h : InRegions X a n) (hl : l ≤ n) :
    InRegions X a l := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega_arith⟩

/-- What `store` does: the block `out` at `D`, and nothing else but the
rounds' memory; `edi` the working space's address. -/
structure MPost (s : State) (S D : BitVec 32) (out : Spec.Cast5.Block) (v : State) : Prop where
  blk : Spec.Cast5.blockAt v.mem (D.setWidth 64) = out
  frame : Frame (blockR D :: blockMem S (s.gpr .esp)) s.mem v.mem
  edi : v.gpr .edi = S
  same : ∀ q, q ∉ roundRegs → v.gpr q = s.gpr q
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  syms : v.syms = s.syms

theorem store_ok {s u : State} {S K D : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : BPre s S K D k n) (hu : RInv s S K k n lr u)
    (hW : InRegions s.wr (S.setWidth 64) 304) (hfit : S.toNat + 304 ≤ 2 ^ 32)
    (hDm : Region.Disjoint (blockR D) ⟨S.setWidth 64 + BitVec.ofNat 64 280, 8⟩) :
    WP isa (.block Modes.store) u (MPost s S D (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have c := hu.ctx
  obtain uD : u.mem.readW (addr S dataOff) 32 = D := by
    rw [slot_frame c.fitS hu.frame (fun r hr => (blockMem_disjoint h.ctx r hr).2.2) (by decide) (by decide)]
    exact h.dataSlot
  obtain ⟨X, hX⟩ : ∃ X, u.mem.readW (addr S 280) 32 = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, u.mem.readW (addr S 284) 32 = Y := ⟨_, rfl⟩
  obtain w0 : InRegions u.wr (addr D 0) 4 := by
    rw [addr_D0 h.fitD, hu.wr]
    obtain ⟨g, hg, hc⟩ := h.wD
    exact ⟨g, hg, by unfold Region.Contains at hc ⊢; omega_arith⟩
  obtain w4 : InRegions u.wr (addr D 4) 4 := by
    rw [addr_off h.fitD 4 (by decide), hu.wr]
    exact CallLay.inRegions_sub h.wD (by omega_arith) (by decide)
  obtain mW : ∀ e, e + 4 ≤ 304 → InRegions u.wr (addr S e) 4 := fun e he => by
    rw [addr_eq (by omega_arith), hu.wr]; exact CallLay.inRegions_sub hW he (by decide)
  obtain mR : ∀ e, e + 4 ≤ 304 → InRegions (u.rd ++ u.wr) (addr S e) 4 := fun e he => by
    obtain ⟨g, hg, hc⟩ := mW e he; exact ⟨g, List.mem_append_right _ hg, hc⟩
  obtain rdD := mR dataOff (by decide)
  obtain rdX := mR 280 (by decide)
  obtain rdY := mR 284 (by decide)
  obtain wX := mW 280 (by decide)
  obtain wY := mW 284 (by decide)
  have hbx := hu.bx
  have hbp := hu.bp
  obtain ⟨m', hm'⟩ : ∃ m', (u.mem.writeW (addr D 0) (byteRev32 lr.2)).writeW (addr D 4) (byteRev32 lr.1) = m' :=
    ⟨_, rfl⟩
  have sm (e : Nat) (h1 : 280 ≤ e) (h2 : e + 4 ≤ 288) : m'.readW (addr S e) 32 = u.mem.readW (addr S e) 32 := by
    have hs (o : Nat) (ho : o + 4 ≤ 8) : Mem.Sep (addr S e) 4 (addr D o) 4 := by
      refine Region.Disjoint.sep hDm.symm ?_ ?_
      · rw [addr_eq (by omega_arith)]; exact Offset.contains _ h1 (by omega_arith) (by omega_arith)
      · rw [addr_off h.fitD o (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [← hm', Mem.readW_writeW_sep (w' := 32) (hs 4 (by decide)) (by decide),
      Mem.readW_writeW_sep (w' := 32) (hs 0 (by decide)) (by decide)]
  obtain e : (m'.writeW (addr S 280) X).writeW (addr S 284) Y = m' := by
    rw [← hX, ← sm 280 (by decide) (by decide), writeW_readW, ← hY, ← sm 284 (by decide) (by decide),
      writeW_readW]
  unfold Modes.store
  refine wp_ldm (b := .esi) (B := S) (o := dataOff) c.si rdD fun u₁ v₁ => ?_
  obtain si₁ : u₁.gpr .esi = S := (v₁.other _ (by decide)).trans c.si
  refine wp_ldm (b := .esi) (B := S) (o := 4 * dSlot) si₁ (by rw [v₁.rd, v₁.wr]; exact rdX) fun u₂ v₂ => ?_
  obtain si₂ : u₂.gpr .esi = S := (v₂.other _ (by decide)).trans si₁
  refine wp_ldm (b := .esi) (B := S) (o := 4 * nSlot) si₂ (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr]; exact rdY)
    fun u₃ v₃ => ?_
  refine wp_bswap fun u₄ v₄ => ?_
  obtain dx₄ : u₄.gpr .edx = D := by
    rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, uD]
  refine wp_stm (b := .edx) (B := D) (o := 0) dx₄ (by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact w0) fun u₅ v₅ => ?_
  refine wp_bswap fun u₆ v₆ => ?_
  refine wp_stm (b := .edx) (B := D) (o := 4) (by rw [v₆.other _ (by decide), v₅.gpr]; exact dx₄)
    (by rw [v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact w4) fun u₇ v₇ => ?_
  obtain si₆ : u₆.gpr .esi = S := by
    rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide)]; exact si₂
  refine wp_stm (b := .esi) (B := S) (o := 4 * dSlot) (by rw [v₇.gpr]; exact si₆)
    (by rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact wX) fun u₈ v₈ => ?_
  refine wp_stm (b := .esi) (B := S) (o := 4 * nSlot) (by rw [v₈.gpr, v₇.gpr]; exact si₆)
    (by rw [v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact wY) fun u₉ v₉ => ?_
  refine wp_mov fun u₁₀ v₁₀ => WP.block_nil ?_
  obtain g₉ : ∀ r, u₉.gpr r = u₆.gpr r := fun r => by rw [v₉.gpr, v₈.gpr, v₇.gpr]
  obtain bp₄ : u₄.gpr .ebp = byteRev32 lr.2 := by
    rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hbp]; rfl
  obtain bx₆ : u₆.gpr .ebx = byteRev32 lr.1 := by
    rw [v₆.gpr, v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), hbx]; rfl
  obtain ax₆ : u₆.gpr .eax = X := by
    rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem]; exact hX
  obtain cx₆ : u₆.gpr .ecx = Y := by
    rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem]; exact hY
  obtain m₁₀ : u₁₀.mem = m' := by
    rw [v₁₀.mem, v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    simp only [v₈.gpr, v₇.gpr, ax₆, cx₆, bx₆, bp₄]
    rw [show 4 * dSlot = 280 from rfl, show 4 * nSlot = 284 from rfl, hm', e]
  refine ⟨?_, ?_, ?_, fun q hq => ?_, by rw [v₁₀.rd, v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hu.rd],
    by rw [v₁₀.wr, v₉.wr, v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, hu.wr],
    by rw [v₁₀.syms, v₉.syms, v₈.syms, v₇.syms, v₆.syms, v₅.syms, v₄.syms, v₃.syms, v₂.syms, v₁.syms, hu.syms]⟩
  · rw [m₁₀, ← hm', addr_D0 h.fitD, addr_off h.fitD 4 (by decide), blockAt_write]
  · rw [m₁₀, ← hm']
    obtain c0 : (blockR D).Contains (addr D 0) (32 / 8) := by
      rw [addr_D0 h.fitD]; simp [Region.Contains]
    obtain c4 : (blockR D).Contains (addr D 4) (32 / 8) := by
      rw [addr_off h.fitD 4 (by decide)]; exact Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by decide) (by decide)
    obtain f1 := (hu.frame.mono (rs' := blockR D :: blockMem S (s.gpr .esp))
      (fun r hr => List.mem_cons_of_mem _ hr)).writeW List.mem_cons_self (byteRev32 lr.2) c0
    exact f1.writeW List.mem_cons_self (byteRev32 lr.1) c4
  · rw [v₁₀.gpr, g₉]; exact si₆
  · have a : q ≠ .edx := fun e => hq (by rw [e]; decide)
    obtain b : q ≠ .eax := fun e => hq (by rw [e]; decide)
    obtain d : q ≠ .ecx := fun e => hq (by rw [e]; decide)
    obtain f : q ≠ .edi := fun e => hq (by rw [e]; decide)
    obtain g : q ≠ .ebx := fun e => hq (by rw [e]; decide)
    obtain i : q ≠ .ebp := fun e => hq (by rw [e]; decide)
    rw [v₁₀.other _ f, g₉, v₆.other _ g, v₅.gpr, v₄.other _ i, v₃.other _ d, v₂.other _ b, v₁.other _ a]
    exact hu.same q hq

/-- The direction's cipher on the 8 bytes at `p` is the block's. -/
theorem dirCipher_bytes (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (m : Mem) (p : Addr) :
    dirCipher up k n (Spec.Aes.bytesAt m p 8) =
      (VG.Proof.Cast5.X86.cipher up k n (Spec.Cast5.blockAt m p)).toList := by
  cases up <;> simp only [dirCipher, VG.Proof.Cast5.X86.cipher, Spec.Cast5.cipher, Spec.Cast5.invCipher,
    ofFn_bytesAt, Bool.false_eq_true, ite_true, ite_false]

theorem toNat_add32 {B : BitVec 32} {d : Nat} (h : B.toNat + d < 2 ^ 32) :
    (B + BitVec.ofNat 32 d).toNat = B.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : d < 2 ^ 32), Nat.mod_eq_of_lt h]

theorem crypt_wp (up : Bool) {s : State} {B : BitVec 32} {kn : Spec.Cast5.Schedule × Nat}
    (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B (dirCore up).total) (hr : Ready s B kn)
    (hst : (dirCore up).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore up).crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Ready s' B kn ∧
      Frame [coreRegion (dirCore up) B, stkRegion (s.gpr .esp) (dirCore up).stack] s.mem s'.mem ∧
      (∀ j < (dirCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw) =
        dirCipher up kn.1 kn.2 (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨k, n⟩ := kn
  obtain ⟨K, hb, hsd⟩ := hr
  have hw := hs.wr
  have hfB := hs.fit
  rw [dirCore_total] at hw hfB
  have hB' : s.gpr .edi = B := hB
  obtain ⟨dKB, dTB, dAB⟩ := hb.dW _ hw
  obtain aE4 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := inRegions_prefix hb.inA (by decide)
  obtain aE8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := by
    rw [addr8 hb.fitE]; exact CallLay.inRegions_sub hb.inA (by decide) (by decide)
  obtain aB : ∀ e, e < 4 * 76 → addr B e = B.setWidth 64 + BitVec.ofNat 64 e := fun e he => addr_eq (by omega_arith)
  obtain sW : ∀ e, e + 4 ≤ 4 * 76 → InRegions s.wr (addr B e) 4 := fun e he => by
    rw [aB e (by omega_arith)]; exact ⟨_, hw, Offset.contains_base _ he (by omega_arith)⟩
  -- The slots `48 … 59` of the working space.
  obtain inSl : ∀ e, 48 ≤ e → e + 4 ≤ 60 → (⟨B.setWidth 64, 4 * 66⟩ : Region).Contains (addr B e) (32 / 8) :=
    fun e h1 h2 => by rw [aB e (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  show WP isa (.seq (.block Modes.setup) (.seq (.block load)
    (.seq (if up then encryptBlock else decryptBlock) (.block Modes.store)))) s _
  refine WP.seq ?_
  refine wp_mov fun s₁ u₁ => ?_
  refine wp_ldm (b := .esp) (B := s.gpr .esp) (o := 4) (u₁.other _ (by decide)) (by rw [u₁.rd, u₁.wr]; exact aE4)
    fun s₂ u₂ => ?_
  obtain si₂ : s₂.gpr .esi = B := by rw [u₂.other _ (by decide), u₁.gpr]; exact hB'
  refine wp_stm (b := .esi) (B := B) (o := schedOff) si₂ (by rw [u₂.wr, u₁.wr]; exact sW _ (by decide))
    fun s₃ u₃ => ?_
  refine wp_ldm (b := .esp) (B := s.gpr .esp) (o := 8)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact aE8) fun s₄ u₄ => ?_
  obtain si₄ : s₄.gpr .esi = B := by rw [u₄.other _ (by decide), u₃.gpr]; exact si₂
  refine wp_stm (b := .esi) (B := B) (o := roundsOff) si₄ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sW _ (by decide))
    fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => ?_
  obtain si₇ : s₇.gpr .esi = B := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; exact si₄
  refine wp_stm (b := .esi) (B := B) (o := dataOff) si₇
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sW _ (by decide)) fun s₈ u₈ => WP.block_nil ?_
  -- The state after the setup.
  obtain esp₈ : s₈.gpr .esp = s.gpr .esp := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain sy₈ : s₈.syms = s.syms := by
    rw [u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  obtain si₈ : s₈.gpr .esi = B := by rw [u₈.gpr]; exact si₇
  obtain edi₈ : s₈.gpr .edi = B := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB'
  obtain ax₂ : s₂.gpr .eax = K := by rw [u₂.gpr, u₁.mem]; exact hb.argK
  obtain sepA : ∀ e, 48 ≤ e → e + 4 ≤ 60 → Mem.Sep (addr (s.gpr .esp) 8) 4 (addr B e) 4 := fun e h1 h2 =>
    Region.Disjoint.sep dAB (argR_contains8 hb.fitE) (by rw [aB e (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith))
  obtain ax₄ : s₄.gpr .eax = BitVec.ofNat 32 n := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, ax₂, Mem.readW_writeW_sep (w' := 32) (sepA schedOff (by decide) (by decide)) (by decide)]
    exact hb.argN
  obtain ax₇ : s₇.gpr .eax = B + BitVec.ofNat 32 256 := by rw [u₇.gpr, u₆.gpr, u₅.gpr, si₄]; rfl
  obtain m₈ : s₈.mem = ((s.mem.writeW (addr B schedOff) K).writeW (addr B roundsOff) (BitVec.ofNat 32 n)).writeW
      (addr B dataOff) (B + BitVec.ofNat 32 256) := by
    rw [u₈.mem, ax₇, u₇.mem, u₆.mem, u₅.mem, ax₄, u₄.mem, u₃.mem, ax₂, u₂.mem, u₁.mem]
  -- The setup writes the slots `48 … 59` only.
  obtain slR : Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩ ⟨B.setWidth 64, 4 * 66⟩ :=
    Offset.sub_base _ (by decide)
  obtain inSl' : ∀ e, 48 ≤ e → e + 4 ≤ 60 →
      (⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩ : Region).Contains (addr B e) (32 / 8) :=
    fun e h1 h2 => by rw [aB e (by omega_arith)]; exact Offset.contains _ h1 (by omega_arith) (by omega_arith)
  obtain f₈ : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩] s.mem s₈.mem := by
    rw [m₈]
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (inSl' 48 (by decide) (by decide))).writeW
      List.mem_cons_self _ (inSl' 52 (by decide) (by decide))).writeW List.mem_cons_self _
      (inSl' 56 (by decide) (by decide))
  obtain coreScr : Region.Sub ⟨B.setWidth 64, 4 * 66⟩ ⟨B.setWidth 64, 4 * 76⟩ := Region.sub_prefix (by decide)
  obtain slScr : Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩ ⟨B.setWidth 64, 4 * 76⟩ :=
    Offset.sub_base _ (by decide)
  obtain dSl : ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩ : Region)], (keyR K).Disjoint r ∧
      (tabR s).Disjoint r ∧ (argR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨dKB.sub_right slScr, dTB.sub_right slScr, dAB.sub_right slScr⟩
  obtain hb₈ : Base s₈ K k n := hb.frame esp₈ rd₈ wr₈ sy₈ f₈ dSl
  obtain sep48 : ∀ d e, d + 4 ≤ e ∨ e + 4 ≤ d → d < 256 → e < 256 → Mem.Sep (addr B d) 4 (addr B e) 4 :=
    fun d e h hd he => slot_sep (by omega_arith) hd he h (by decide) (by decide)
  obtain rB : Region.Sub ⟨B.setWidth 64, 256⟩ ⟨B.setWidth 64, 4 * 76⟩ := Region.sub_prefix (by decide)
  obtain eD : (B + BitVec.ofNat 32 256).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 256 := aB 256 (by decide)
  obtain blkSub : Region.Sub (blockR (B + BitVec.ofNat 32 256)) ⟨B.setWidth 64, 4 * 66⟩ := by
    show Region.Sub ⟨(B + BitVec.ofNat 32 256).setWidth 64, 8⟩ _
    rw [eD]; exact Offset.sub_base _ (by decide)
  obtain hpre : BPre s₈ B K (B + BitVec.ofNat 32 256) k n := by
    refine ⟨⟨si₈, by omega_arith, ?_, ?_, ?_, hb.nv, hb.fitK, hb₈.inK, fun j hj => ?_, by rw [esp₈]; exact hb.sp,
      by rw [esp₈]; exact (hsd.sub_right rB).symm, hb₈.dKs, dKB.sub_right rB, hb₈.fitT, hb₈.inT, hb₈.dTs,
      by rw [sy₈]; exact dTB.sub_right rB, tabAt_of_held hb₈.held⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [wr₈]; exact ⟨_, hw, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith⟩
    · rw [m₈, Mem.readW_writeW_sep (w' := 32) (sep48 48 56 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (w' := 32) (sep48 48 52 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32]
    · rw [m₈, Mem.readW_writeW_sep (w' := 32) (sep48 52 56 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32]
    · rw [← Proof.Cast5.scheduleAt_getD _ _ hj, hb₈.sk]
    · rw [m₈, Mem.readW_writeW_self32]
    · rw [toNat_add32 (by omega_arith)]; omega_arith
    · rw [wr₈, eD]; exact ⟨_, hw, Offset.contains_base _ (by decide) (by omega_arith)⟩
    · show Region.Disjoint ⟨(B + BitVec.ofNat 32 256).setWidth 64, 8⟩ _
      rw [eD]; exact Offset.disjoint_base _ (by decide) (by omega_arith)
    · exact ((dKB.sub_right coreScr).sub_right blkSub).symm
    · rw [sy₈]; exact ((dTB.sub_right coreScr).sub_right blkSub).symm
    · rw [esp₈]; exact ((hsd.sub_right coreScr).sub_right blkSub).symm
  refine WP.seq (WP.mono (load_ok hpre) fun u₉ ⟨c₉, hlr, m₉, g₉, rd₉, wr₉, sy₉⟩ => ?_)
  obtain esp₉ : u₉.gpr .esp = s.gpr .esp := (g₉ .esp (by decide)).trans esp₈
  obtain hb₉ : BPre u₉ B K (B + BitVec.ofNat 32 256) k n := ⟨c₉, by rw [m₉]; exact hpre.dataSlot, hpre.fitD,
    by rw [wr₉]; exact hpre.wD, hpre.dDS, hpre.dDK, by rw [sy₉]; exact hpre.dDT,
    by rw [esp₉, ← esp₈]; exact hpre.dDsp⟩
  obtain ⟨lr, hlr'⟩ : ∃ lr, Spec.Cast5.decodeBlock
      (Spec.Cast5.blockAt s₈.mem ((B + BitVec.ofNat 32 256).setWidth 64)) = lr := ⟨_, rfl⟩
  rw [hlr'] at hlr
  obtain hbx : u₉.gpr .ebx = lr.1 := by rw [← hlr]
  obtain hbp : u₉.gpr .ebp = lr.2 := by rw [← hlr]
  obtain hW₉ : InRegions u₉.wr (B.setWidth 64) 304 := by
    rw [wr₉, wr₈]; exact ⟨_, hw, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith⟩
  obtain hDm : (blockR (B + BitVec.ofNat 32 256)).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 280, 8⟩ := by
    show Region.Disjoint ⟨(B + BitVec.ofNat 32 256).setWidth 64, 8⟩ _
    rw [eD]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  obtain hsm : (below (u₉.gpr .esp) 4).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 280, 8⟩ := by
    rw [esp₉]; exact hsd.sub_right (Offset.sub_base _ (by decide))
  have stkEq : stkRegion (s.gpr .esp) (dirCore up).stack = below (s.gpr .esp) 4 := rfl
  have post (v : State) (hv : RInv u₉ B K k n (fold up k n lr) v) :
      WP isa (.block Modes.store) v fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
        Ready s' B (k, n) ∧
        Frame [coreRegion (dirCore up) B, stkRegion (s.gpr .esp) (dirCore up).stack] s.mem s'.mem ∧
        (∀ j < (dirCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw) =
          dirCipher up (k, n).1 (k, n).2 (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw))) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine WP.mono (store_ok hb₉ hv hW₉ (by omega_arith) hDm) fun w hw' => ?_
    obtain espw : w.gpr .esp = s.gpr .esp := (hw'.same .esp (by decide)).trans esp₉
    obtain fall : Frame [coreRegion (dirCore up) B, stkRegion (s.gpr .esp) (dirCore up).stack] s.mem w.mem := by
      refine (f₈.sub fun r hr => ?_).trans ?_
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, slR⟩
      · rw [← m₉]
        refine hw'.frame.sub fun r hr => ?_
        simp only [blockMem, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self, blkSub⟩
        · rw [esp₉]; exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
        · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by simp [dirCore, coreSlots])⟩
        · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by simp [dirCore, coreSlots, kpOff])⟩
    obtain dAll : ∀ r ∈ [coreRegion (dirCore up) B, stkRegion (s.gpr .esp) (dirCore up).stack],
        (keyR K).Disjoint r ∧ (tabR s).Disjoint r ∧ (argR s).Disjoint r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dKB.sub_right coreScr, dTB.sub_right coreScr, dAB.sub_right coreScr⟩
      · exact ⟨hb.dKs, hb.dTs, hb.dAs⟩
    refine ⟨hw'.edi, espw, ⟨K, hb.frame espw (hw'.rd.trans (rd₉.trans rd₈)) (hw'.wr.trans (wr₉.trans wr₈))
      (hw'.syms.trans (sy₉.trans sy₈)) fall dAll, by simp only [stk, espw]; exact hsd⟩, fall, fun j hj => ?_,
      hw'.rd.trans (rd₉.trans rd₈), hw'.wr.trans (wr₉.trans wr₈)⟩
    obtain hj0 : j = 0 := by simp only [dirCore] at hj; omega_arith
    subst hj0
    obtain eB : blkAddr (dirCore up) B 0 = B.setWidth 64 + BitVec.ofNat 64 256 := by
      simp [blkAddr, slotA, dirCore, bufSlot]
    obtain dBlk : ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩ : Region)],
        Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 256, 8⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    rw [show 4 * (dirCore up).bw = 8 from rfl, eB, bytesAt_eq, ← eD, hw'.blk, dirCipher_bytes, cipher_eq,
      eD, ← blockAt_frame f₈ dBlk, ← eD, hlr']
  cases up
  · exact WP.seq (WP.mono (decryptBlock_ok c₉ hbx hbp) fun v hv => post v hv)
  · exact WP.seq (WP.mono (encryptBlock_ok c₉ hbx hbp) fun v hv => post v hv)

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (up : Bool) : (dirCore up).bw = 2 := rfl

/-- CAST5's core, encrypting (`up`) or decrypting, meets what the modes need. -/
def dirCoreSpec (up : Bool) : CoreSpec (dirCore up) where
  Key := Spec.Cast5.Schedule × Nat
  cipher kn := dirCipher up kn.1 kn.2
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len kn b := dirCipher_length up kn.1 kn.2 b
  layout := ⟨by simp [dirCore], .inl rfl, by simp [dirCore, coreSlots, bufSlot], by simp [dirCore]⟩
  keyArgs_congr := keyArgs_congr
  ready_frame h hesp hrd hwr hsy hf hsub _ := ready_frame h hesp hrd hwr hsy hf hsub
  prepare_wp := prepare_wp up
  crypt_wp := crypt_wp up

end VG.Proof.Cast5.X86.Mode

end

end

/-!
# CAST5-CBC, -OFB and -CFB64 on x86 (32-bit): correctness

`cbcEncryptChained_wp`, …, `cfbDecrypt_wp`: the modes' CBC that updates
the chaining value, OFB and CFB (`Proof.Modes.X86.cbcEncChained_wp`, …)
over CAST5's core (`Mode.dirCoreSpec`), with the working space as a sixth
argument (`modeX ivw post`: the chaining value is writable if `ivw`, as it
is for all of them). The table of S-boxes is readable, where the static
`VG_CAST5_S1234` puts it, and holds the S-boxes (`Held`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.ModeFns

open VG VG.X86 VG.Impl.Cast5.X86.Modes VG.Impl.Modes
open VG.Impl.Cast5 (s1234Sym s1234)
open VG.Proof.Modes.X86 (SeqPre stkRegion cbcEncChained_wp cbcDecChained_wp ofb_wp cfbEnc_wp cfbDec_wp)
open VG.Proof.Cast5.X86.Mode (dirCoreSpec KeyArgs Base)
open VG.Proof.Cast5 (Held)

/-- The subkeys. -/
abbrev keyA (s : State) : Region := ⟨(arg s 0).setWidth 64, 128⟩
/-- The chaining value. -/
abbrev ivA (s : State) : Region := ⟨(arg s 2).setWidth 64, 8⟩
/-- The data. -/
abbrev dataA (s : State) : Region := ⟨(arg s 3).setWidth 64, 8 * (arg s 4).toNat⟩
/-- The working space. -/
abbrev scrA (s : State) : Region := ⟨(arg s 5).setWidth 64, 304⟩
/-- The arguments. -/
abbrev argsA (s : State) : Region := ⟨argAddr s 0, 24⟩
/-- The table of S-boxes. -/
abbrev tabA (s : State) : Region := ⟨(s.syms s1234Sym).setWidth 64, 4096⟩
/-- The return address. -/
abbrev retA (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
/-- The word below `esp`, which the core's scans use. -/
abbrev stkA (s : State) : Region := below (s.gpr .esp) 4

/-- The readable regions: the chaining value too unless it is written. -/
def rdL : Bool → State → List Region
  | false, s => [keyA s, ivA s, argsA s, tabA s]
  | true, s => [keyA s, argsA s, tabA s]

/-- The writable regions: the chaining value too if it is written. -/
def wrL : Bool → State → List Region
  | false, s => [dataA s, scrA s]
  | true, s => [dataA s, ivA s, scrA s]

/-- A mode's precondition on x86, with the working space as the sixth
argument, the chaining value writable if `ivw`. -/
structure MPre (ivw : Bool) (s : State) : Prop where
  rdEq : s.rd = rdL ivw s
  wrEq : s.wr = wrL ivw s
  sp : 4 ≤ (s.gpr .esp).toNat
  espFit : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  nv : (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 16
  fitK : (arg s 0).toNat + 128 ≤ 2 ^ 32
  fitV : (arg s 2).toNat + 8 ≤ 2 ^ 32
  fitD : (arg s 3).toNat + 8 * (arg s 4).toNat ≤ 2 ^ 32
  fitS : (arg s 5).toNat + 304 ≤ 2 ^ 32
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  held : Held s.mem ((s.syms s1234Sym).setWidth 64) s1234
  dDS : (dataA s).Disjoint (scrA s)
  dVS : (ivA s).Disjoint (scrA s)
  dVD : ivw = true → (ivA s).Disjoint (dataA s)
  dKw : ∀ r ∈ s.wr, (keyA s).Disjoint r
  dTw : ∀ r ∈ s.wr, (tabA s).Disjoint r
  dAw : ∀ r ∈ s.wr, (argsA s).Disjoint r
  dRw : ∀ r ∈ s.wr, (retA s).Disjoint r
  dSw : ∀ r ∈ s.wr, (stkA s).Disjoint r
  dKs : (keyA s).Disjoint (stkA s)
  dTs : (tabA s).Disjoint (stkA s)

/-- A mode on x86 with the precondition `MPre ivw` and the postcondition
`post`. -/
def modeX (ivw : Bool) (post : State → State → Prop) : Contract isa where
  pre := MPre ivw
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧
    s₁.syms s1234Sym = s₂.syms s1234Sym

section
variable {ivw : Bool} {s : State}

theorem MPre.mem_wr_data (h : MPre ivw s) : dataA s ∈ s.wr := by
  rw [h.wrEq]; cases ivw <;> simp [wrL]
theorem MPre.mem_wr_scr (h : MPre ivw s) : scrA s ∈ s.wr := by
  rw [h.wrEq]; cases ivw <;> simp [wrL]
theorem MPre.mem_wr_iv (h : MPre ivw s) (hw : ivw = true) : ivA s ∈ s.wr := by
  rw [h.wrEq]; subst hw; simp [wrL]
theorem MPre.mem_iv (h : MPre ivw s) : ivA s ∈ s.rd ++ s.wr := by
  rw [h.rdEq, h.wrEq]; cases ivw <;> simp [rdL, wrL]
theorem MPre.mem_args (h : MPre ivw s) : argsA s ∈ s.rd ++ s.wr := by
  rw [h.rdEq]; cases ivw <;> simp [rdL]
theorem MPre.mem_key (h : MPre ivw s) : keyA s ∈ s.rd ++ s.wr := by
  rw [h.rdEq]; cases ivw <;> simp [rdL]
theorem MPre.mem_tab (h : MPre ivw s) : tabA s ∈ s.rd ++ s.wr := by
  rw [h.rdEq]; cases ivw <;> simp [rdL]

/-- The word below `esp` is apart from the arguments and the return address. -/
theorem stk_apart (h : MPre ivw s) :
    Region.Disjoint (stkA s) (argsA s) ∧ Region.Disjoint (stkA s) (retA s) := by
  have hlo := h.sp
  have hfit := h.espFit
  have e : (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 :=
    VG.X86.Taint.sub_setWidth hlo
  have ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [hfit])
  refine ⟨?_, ?_⟩
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ ⟨argAddr s 0, 24⟩
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by decide)
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ _
    have := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 4) (a := 0) (l := 4) (by decide)
    rw [BitVec.add_zero] at this
    rw [e]; exact this

end

theorem scr_eq (up : Bool) (s : State) : Modes.X86.scrR s (dirCore up) = scrA s := rfl

/-- `MPre`'s precondition gives the modes'. -/
theorem seqPre_of (up : Bool) {ivw : Bool} {M : Mode} (hstep : M.step = 8) (hiv : M.ivOut = ivw) {s : State}
    (h : MPre ivw s) : SeqPre (dirCore up) M s := by
  have hL := (dirCoreSpec up).layout
  obtain ⟨sA, sR⟩ := stk_apart h
  have mS := h.mem_wr_scr
  have mD := h.mem_wr_data
  refine ⟨h.mem_args, h.espFit, ⟨mS, h.fitS⟩, h.mem_iv, fun hv => h.mem_wr_iv (hiv ▸ hv), h.fitV,
    by rw [hstep]; exact mD, by rw [hstep]; exact h.fitD, by rw [hstep]; exact h.dDS, h.dVS,
    fun hv => by rw [hstep]; exact h.dVD (hiv ▸ hv), h.dAw _ mS, by rw [hstep]; exact h.dAw _ mD,
    h.dRw _ mS, by rw [hstep]; exact h.dRw _ mD, fun hv => ?_, by rw [hstep]; exact h.dSw _ mD,
    (h.dSw _ mS).sub_right (VG.Offset.sub_base _ (by simp [dirCore, coreSlots])), sA, sR, h.sp,
    by rw [hstep]; simp [dirCore], hL⟩
  exact h.dRw _ (h.mem_wr_iv (hiv ▸ hv))

theorem keyArgs_of (up : Bool) {ivw : Bool} {s : State} (h : MPre ivw s) :
    KeyArgs s [Modes.X86.scrR s (dirCore up)]
      (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64), (arg s 1).toNat) := by
  obtain ⟨sA, -⟩ := stk_apart h
  have hfit := h.espFit
  have ea : ∀ k, k + 4 ≤ 24 → (⟨addr (s.gpr .esp) (4 + k), 4⟩ : Region).Sub (argsA s) := by
    intro k hk
    have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [hfit])
    have ek : addr (s.gpr .esp) (4 + k) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 k := by
      rw [addr_eq (by omega_using [hfit, hk]), VG.Offset.add_add]
    show Region.Sub ⟨addr (s.gpr .esp) (4 + k), 4⟩ ⟨argAddr s 0, 24⟩
    rw [e0, ek]; exact VG.Offset.sub_base _ hk
  have argSub : (Mode.argR s).Sub (argsA s) := by
    have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [hfit])
    show Region.Sub ⟨addr (s.gpr .esp) 4, 8⟩ ⟨argAddr s 0, 24⟩
    rw [e0, show addr (s.gpr .esp) 4 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 0 by
      rw [BitVec.add_zero]; exact addr_eq (by omega_using [hfit])]
    exact VG.Offset.sub_base _ (by decide)
  have mS := h.mem_wr_scr
  refine ⟨arg s 0, ⟨by omega_using [hfit], h.sp, ⟨_, h.mem_args, by
      show (⟨argAddr s 0, 24⟩ : Region).Contains (argAddr s 0) 8
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []⟩, rfl, ?_, h.nv, h.fitK, ⟨_, h.mem_key,
    Region.contains_self _ _⟩, rfl, h.fitT, ⟨_, h.mem_tab, Region.contains_self _ _⟩, h.held,
    fun r hr => ⟨h.dKw r hr, h.dTw r hr, (h.dAw r hr).sub_left argSub⟩, h.dKs, h.dTs,
    (sA.symm.sub_left argSub)⟩, fun r hr => ?_⟩
  · show arg s 1 = BitVec.ofNat 32 (arg s 1).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact ⟨h.dKw _ mS, h.dTw _ mS, (h.dAw _ mS).sub_left argSub, h.dSw _ mS⟩

/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) :=
  Spec.Cast5.cbcBlocksAt m ((arg s 3).setWidth 64) (arg s 4).toNat
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m ((arg s 2).setWidth 64) 8
/-- CAST5 encryption under the key of `s`. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.Cast5.cipher (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64)) (arg s 1).toNat
/-- CAST5 decryption under the key of `s`. -/
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Cast5.invCipher (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64)) (arg s 1).toNat

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (arg s 4).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

@[simp] theorem dirCore_ka (up : Bool) : (dirCore up).ka = 2 := rfl

theorem data_eq (m : Mem) (s : State) :
    Proof.Modes.chunksAt 8 m ((arg s 3).setWidth 64) (arg s 4).toNat = dataAt m s :=
  (Proof.Cast5.cbcBlocksAt_eq _ _ _).symm
theorem iv_eq (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 2).setWidth 64) 8 = ivAt m s := rfl
theorem cipher_eq (s : State) :
    (dirCoreSpec true).cipher (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64), (arg s 1).toNat) = ciph s := rfl
theorem invCipher_eq (s : State) :
    (dirCoreSpec false).cipher (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64), (arg s 1).toNat) =
      invCiph s := rfl

tactic_template "post_eq_cast5_x86_modesverified" h:ident : tactic =>
  `(tactic| simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp,
                     Proof.Modes.X86.P, Proof.Modes.X86.N, dirCore_ka, Mode.dirCore_bw, Nat.reduceMul, Nat.reduceAdd,
                     data_eq, iv_eq, cipher_eq, invCipher_eq] at $h:ident)

theorem cbcEncryptChained_wp {s₀ : State} (hp : (modeX true cbcEncPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (modeX true cbcEncPost).post s₀ s' :=
  WP.mono (cbcEncChained_wp (dirCoreSpec true) (seqPre_of true rfl rfl hp) (keyArgs_of true hp))
    fun _ ⟨h1, h2, h3⟩ => by post_eq_cast5_x86_modesverified h2; post_eq_cast5_x86_modesverified h3; exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_wp {s₀ : State} (hp : (modeX true cbcDecPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (modeX true cbcDecPost).post s₀ s' :=
  WP.mono (cbcDecChained_wp (dirCoreSpec false) (seqPre_of false rfl rfl hp) (keyArgs_of false hp))
    fun _ ⟨h1, h2, h3⟩ => by post_eq_cast5_x86_modesverified h2; post_eq_cast5_x86_modesverified h3; exact ⟨h1, h2, h3⟩

theorem ofb_wp_x86 {s₀ : State} (hp : (modeX true ofbPost).pre s₀) :
    WP isa ofb s₀ fun s' => abiPreserved s₀ s' ∧ (modeX true ofbPost).post s₀ s' :=
  WP.mono (ofb_wp (dirCoreSpec true) (seqPre_of true rfl rfl hp) (keyArgs_of true hp))
    fun _ ⟨h1, h2, h3⟩ => by post_eq_cast5_x86_modesverified h2; post_eq_cast5_x86_modesverified h3; exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : (modeX true cfbEncPost).pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (modeX true cfbEncPost).post s₀ s' :=
  WP.mono (cfbEnc_wp (dirCoreSpec true) (seqPre_of true rfl rfl hp) (keyArgs_of true hp))
    fun _ ⟨h1, h2, h3⟩ => by post_eq_cast5_x86_modesverified h2; post_eq_cast5_x86_modesverified h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : (modeX true cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (modeX true cfbDecPost).post s₀ s' :=
  WP.mono (cfbDec_wp (dirCoreSpec true) (seqPre_of true rfl rfl hp) (keyArgs_of true hp))
    fun _ ⟨h1, h2, h3⟩ => by post_eq_cast5_x86_modesverified h2; post_eq_cast5_x86_modesverified h3; exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

/-- The initial taint of the modes: `esp` public, the words holding `data`,
`iv` and `scratch` known to be the base addresses of the writable regions,
and room for the core's word below `esp`. -/
def τFb : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8, 304], argLen := 28,
    argBases := [(16, 0), (12, 1), (24, 2)], room := 4 }

theorem stk_eq (s : State) (h : 4 ≤ (s.gpr .esp).toNat) :
    (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ : Region) = stkA s := by
  show _ = (⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ : Region)
  rw [VG.X86.Taint.sub_setWidth h]

theorem τFb_wf {s : State} (h : MPre true s) : VG.X86.Taint.Wf τFb s := by
  have hw := h.wrEq
  simp only [wrL] at hw
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [τFb]; have := h.espFit; omega_using [this], ?_⟩, ?_⟩ ?_
  · rw [hw]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨(h.dVD rfl).symm, h.dDS⟩, h.dVS, fun _ h => h.elim⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · simp only [toNat_setWidth]; exact h.fitD
    · simp only [toNat_setWidth]; exact h.fitV
    · simp only [toNat_setWidth]; exact h.fitS
  · intro r hr
    exact VG.X86.Taint.frame_disjoint (n := 24) (by have := h.espFit; omega_using [this]) (h.dRw r hr) (h.dAw r hr)
  · intro p hp
    simp only [τFb, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hw, addr, arg, argAddr]
  · intro _
    refine ⟨h.sp, fun r hr => ?_⟩
    simp only [τFb]
    rw [stk_eq s h.sp]
    exact h.dSw r hr

theorem argBytes_agree {τ : VG.X86.Taint.T} (hl : τ.argLen = 28) (hstk : τ.stk = []) {s₁ s₂ : State}
    (f₁ : (s₁.gpr .esp).toNat + 28 ≤ 2 ^ 32) (f₂ : (s₂.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    (ha : ∀ i < 6, arg s₁ i = arg s₂ i) {k : Nat} (h4 : 4 ≤ k) (hk : k < τ.argLen) :
    s₁.mem (VG.X86.Taint.argByte s₁ (VG.X86.Taint.depth τ.stk + k)) =
      s₂.mem (VG.X86.Taint.argByte s₂ (VG.X86.Taint.depth τ.stk + k)) := by
  rw [hl] at hk
  rw [hstk, show VG.X86.Taint.depth [] = 0 from rfl, Nat.zero_add]
  rw [VG.X86.Taint.argByte_eq (n := 28) f₁ h4 hk, VG.X86.Taint.argByte_eq (n := 28) f₂ h4 hk,
    Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
  exact congrArg _ (ha _ (by omega_using [hk]))

theorem τFb_agree {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (modeX true post).pre s₁)
    (h₂ : (modeX true post).pre s₂) (hp : (modeX true post).pub s₁ s₂) :
    VG.X86.Taint.AgreeS [s1234Sym] τFb s₁ s₂ := by
  obtain ⟨sp, args, sy⟩ := hp
  refine ⟨⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τFb_wf h₁, τFb_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp,
    fun k h4 hk => argBytes_agree rfl rfl h₁.espFit h₂.espFit args h4 hk⟩, fun n hn => ?_⟩
  · simp only [τFb, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [h₁.wrEq, h₂.wrEq]
    simp only [wrL, dataA, ivA, scrA, args 2 (by decide), args 3 (by decide), args 4 (by decide),
      args 5 (by decide)]
  · simp only [List.mem_singleton] at hn
    subst hn; exact sy

theorem cbcEncryptChained_ct :
    ConstantTime isa (modeX true cbcEncPost).pre (modeX true cbcEncPost).pub cbcEncryptChained :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

theorem cbcDecryptChained_ct :
    ConstantTime isa (modeX true cbcDecPost).pre (modeX true cbcDecPost).pub cbcDecryptChained :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

theorem ofb_ct : ConstantTime isa (modeX true ofbPost).pre (modeX true ofbPost).pub ofb :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbEncrypt_ct : ConstantTime isa (modeX true cfbEncPost).pre (modeX true cfbEncPost).pub cfbEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa (modeX true cfbDecPost).pre (modeX true cfbDecPost).pub cfbDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

open VG.Impl.Cast5 (ecbConsts)
open VG.Proof.Cast5.X86 (ecbConsts_eq s1234_length)

/-! ## Satisfiability -/

/-- The arguments of the witness at `0x8004`: the schedule at `0x1000`, 16
rounds, the chaining value at `0x2000`, no blocks at `0x3000` and the working
space at `0x4000`. -/
def satArgs : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20 else if a = 0x8011 then 0x30
  else if a = 0x8019 then 0x40 else 0

/-- The memory of the witness: the table at `0x100000`, the arguments
elsewhere (irreducible: unfolding it in a definitional check would evaluate
the table). -/
@[irreducible] def satMem : Mem := fun a =>
  if (a - 0x100000).toNat < 4096 then constMem 0x100000 s1234 a else satArgs a

theorem satMem_held : ∀ i < s1234.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  intro i hi
  rw [s1234_length] at hi
  have hm : satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 s1234).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hj])]
    unfold satMem
    rw [e, ite_eq_left (show 8 * i + j < 4096 by omega_using [hi, hj])]
  exact hm.trans (constMem_held 0x100000 s1234 (by rw [s1234_length]; decide) i (by rw [s1234_length]; exact hi))

/-- A state satisfying the modes' precondition, with the chaining value
readable (`ivw = false`) or writable. -/
def satState (ivw : Bool) : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := if ivw then [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩] else [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x100000, 4096⟩]
  wr := if ivw then [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩]
    else [⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩]
  syms _ := 0x100000

theorem sat_arg (ivw : Bool) (j : Nat) (hj : j < 6) : arg (satState ivw) j = satArgs.readW (argAddr (satState ivw) j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMem _ = _
  unfold satMem
  have : ∀ j < 6, ∀ b < 4, ¬ (argAddr (satState ivw) j + BitVec.ofNat 64 b - 0x100000).toNat < 4096 := by
    cases ivw <;> decide
  rw [ite_eq_right (this j hj b (by omega_using [hb]))]

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with `336` bytes of
stack: the schedule at `0x1000`, the chaining value at `0x2000`, no blocks at
`0x3000`, as stack arguments at `0x8004`, which are writable. -/
def frameSat (ivw : Bool) : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := if ivw then [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩] else [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x100000, 4096⟩]
  wr := if ivw then [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] else [⟨0x3000, 0⟩, ⟨0x8004, 20⟩]
  syms _ := 0x100000

theorem frameSat_arg (ivw : Bool) (j : Nat) (hj : j < 5) :
    arg (frameSat ivw) j = satArgs.readW (argAddr (frameSat ivw) j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMem _ = _
  unfold satMem
  have : ∀ j < 5, ∀ b < 4, ¬ (argAddr (frameSat ivw) j + BitVec.ofNat 64 b - 0x100000).toNat < 4096 := by
    cases ivw <;> decide
  rw [ite_eq_right (this j hj b (by omega_using [hb]))]

/-! ## OFB, CFB64 and CBC -/

/-- OFB's, CFB's or CBC's contract (`sig`, `ofbSig`, `cfbSig` or `cbcChainedSig`)
with the working space as a sixth argument, under the calling convention with the table. -/
abbrev fbK (sig : Sig) (pre : Curry (sig.words X86.abi.ptrBits) (Mem → Prop)) (post : sig.Post X86.abi.ptrBits) :
    Contract isa :=
  Sig.scratchContract (X86.abi.withConsts ecbConsts) sig "scratch" .u64 38 pre post true 4

theorem ofb_pre {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} (s : State)
    (h : (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s) :
    MPre true (s.withRegions (rdL true s) (wrL true s)) ∧ s.rd = [keyA s, tabA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrA s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch] at h
  obtain ⟨h4, hsp, hdrop, held, fitT, dTw, -, dTB, -, htake, hwr, dKV, dKD, dKS, -, dVD, dVS, dVA, dDS, dDA, dSA,
    -, dRV, dRD, dRS, -, dBK, dBV, dBD, dBS, -, fK, fV, fD, fS, nv⟩ := h
  have hrd : s.rd = [keyA s, tabA s] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop]; rfl
  have be : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
    simp only [below, VG.X86.Taint.sub_setWidth h4]
  have e8 : (arg s 4).toNat * 8 = 8 * (arg s 4).toNat := Nat.mul_comm _ _
  rw [e8] at hwr dKD dVD dDS dDA dRD dBD fD
  have mV : ivA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mD : dataA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mS : scrA s ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨⟨rfl, rfl, h4, (by show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega_using [hsp]), nv, fK, fV, fD, fS, fitT,
    (fun i hi => held i (by rw [s1234_length] at hi; exact hi)), dDS, dVS, (fun _ => dVD),
    (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dBK.symm),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dTB)⟩, hrd,
    (by rw [← e8] at hwr; exact hwr)⟩
  all_goals
    simp only [State.withRegions_wr, wrL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
  · exact dKD
  · exact dKV
  · exact dKS
  · exact dTw _ mD
  · exact dTw _ mV
  · exact dTw _ mS
  · exact dDA.symm
  · exact dVA.symm
  · exact dSA.symm
  · exact dRD
  · exact dRV
  · exact dRS
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBD
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBV
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBS

theorem ofb_pub {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s₁)
    (_ : (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s₂)
    (h : (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeX true postX).pub (s₁.withRegions (rdL true s₁) (wrL true s₁))
      (s₂.withRegions (rdL true s₂) (wrL true s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
  obtain ⟨hsp, hsy, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hsp, fun i hi => ?_, hsy⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem ofbK_verified {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} {postX : State → State → Prop}
    {c : Prog isa}
    (hwp : ∀ s, (modeX true postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeX true postX).post s s')
    (hct : ConstantTime isa (modeX true postX).pre (modeX true postX).pub c)
    (hpost : ∀ s s', (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdL true s) (wrL true s)) (s'.withRegions (rdL true s) (wrL true s)) →
        (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeX true postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (ofb_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdL true) (wrL true)
    (fun s h => (ofb_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost ofb_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := ofb_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdL, wrL, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := ofb_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrL, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem ofb_sat {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} :
    (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre (satState true) := by
  have a0 : arg (satState true) 0 = 0x1000 := (sat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (satState true) 1 = 16 := (sat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (satState true) 2 = 0x2000 := (sat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (satState true) 3 = 0x3000 := (sat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (satState true) 4 = 0 := (sat_arg true 4 (by decide)).trans (by decide)
  have a5 : arg (satState true) 5 = 0x4000 := (sat_arg true 5 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : satState true = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch]
  subst s
  rw [a0, a1, a2, a3, a4, a5]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem ofb_frameSat (post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbSig.contract (X86.abi.withConsts ecbConsts) (Spec.Cast5.ofbPre X86.abi.ptrBits) post true
      336).pre s := by
  refine ⟨frameSat true, ?_⟩
  have a0 : arg (frameSat true) 0 = 0x1000 := (frameSat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (frameSat true) 1 = 16 := (frameSat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (frameSat true) 2 = 0x2000 := (frameSat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (frameSat true) 3 = 0x3000 := (frameSat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (frameSat true) 4 = 0 := (frameSat_arg true 4 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : frameSat true = s
  sig_pre [Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  rw [a0, a1, a2, a3, a4]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem cfb_pre {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} (s : State)
    (h : (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s) :
    MPre true (s.withRegions (rdL true s) (wrL true s)) ∧ s.rd = [keyA s, tabA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrA s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch] at h
  obtain ⟨h4, hsp, hdrop, held, fitT, dTw, -, dTB, -, htake, hwr, dKV, dKD, dKS, -, dVD, dVS, dVA, dDS, dDA, dSA,
    -, dRV, dRD, dRS, -, dBK, dBV, dBD, dBS, -, fK, fV, fD, fS, nv⟩ := h
  have hrd : s.rd = [keyA s, tabA s] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop]; rfl
  have be : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
    simp only [below, VG.X86.Taint.sub_setWidth h4]
  have e8 : (arg s 4).toNat * 8 = 8 * (arg s 4).toNat := Nat.mul_comm _ _
  rw [e8] at hwr dKD dVD dDS dDA dRD dBD fD
  have mV : ivA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mD : dataA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mS : scrA s ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨⟨rfl, rfl, h4, (by show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega_using [hsp]), nv, fK, fV, fD, fS, fitT,
    (fun i hi => held i (by rw [s1234_length] at hi; exact hi)), dDS, dVS, (fun _ => dVD),
    (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dBK.symm),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dTB)⟩, hrd,
    (by rw [← e8] at hwr; exact hwr)⟩
  all_goals
    simp only [State.withRegions_wr, wrL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
  · exact dKD
  · exact dKV
  · exact dKS
  · exact dTw _ mD
  · exact dTw _ mV
  · exact dTw _ mS
  · exact dDA.symm
  · exact dVA.symm
  · exact dSA.symm
  · exact dRD
  · exact dRV
  · exact dRS
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBD
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBV
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBS

theorem cfb_pub {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s₁)
    (_ : (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s₂)
    (h : (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeX true postX).pub (s₁.withRegions (rdL true s₁) (wrL true s₁))
      (s₂.withRegions (rdL true s₂) (wrL true s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
  obtain ⟨hsp, hsy, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hsp, fun i hi => ?_, hsy⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem cfbK_verified {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} {postX : State → State → Prop}
    {c : Prog isa}
    (hwp : ∀ s, (modeX true postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeX true postX).post s s')
    (hct : ConstantTime isa (modeX true postX).pre (modeX true postX).pub c)
    (hpost : ∀ s s', (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdL true s) (wrL true s)) (s'.withRegions (rdL true s) (wrL true s)) →
        (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeX true postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (cfb_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdL true) (wrL true)
    (fun s h => (cfb_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost cfb_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := cfb_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdL, wrL, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := cfb_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrL, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem cfb_sat {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} :
    (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre (satState true) := by
  have a0 : arg (satState true) 0 = 0x1000 := (sat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (satState true) 1 = 16 := (sat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (satState true) 2 = 0x2000 := (sat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (satState true) 3 = 0x3000 := (sat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (satState true) 4 = 0 := (sat_arg true 4 (by decide)).trans (by decide)
  have a5 : arg (satState true) 5 = 0x4000 := (sat_arg true 5 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : satState true = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch]
  subst s
  rw [a0, a1, a2, a3, a4, a5]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem cfb_frameSat (post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbSig.contract (X86.abi.withConsts ecbConsts) (Spec.Cast5.cfbPre X86.abi.ptrBits) post true
      336).pre s := by
  refine ⟨frameSat true, ?_⟩
  have a0 : arg (frameSat true) 0 = 0x1000 := (frameSat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (frameSat true) 1 = 16 := (frameSat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (frameSat true) 2 = 0x2000 := (frameSat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (frameSat true) 3 = 0x3000 := (frameSat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (frameSat true) 4 = 0 := (frameSat_arg true 4 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : frameSat true = s
  sig_pre [Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  rw [a0, a1, a2, a3, a4]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl


theorem ofb_verified :
    Verified X86.target ofb
      (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) (Proof.Cast5.ofbPost X86.abi.ptrBits)) :=
  ofbK_verified (fun _ hs => ofb_wp_x86 hs) ofb_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, Proof.Cast5.ofbPost, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, ofb_sat⟩

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 ofb)
      (Proof.Cast5.ofbRoundsContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Spec.Cast5.ofbPre X86.abi.ptrBits)
    (post := Proof.Cast5.ofbPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    ofb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.ofbPost_local _) (Proof.Cast5.ofbPostOut_local _) (ofb_frameSat _)

theorem cfbEncrypt_verified :
    Verified X86.target cfbEncrypt
      (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) (Proof.Cast5.cfbEncPost X86.abi.ptrBits)) :=
  cfbK_verified (fun _ hs => cfbEncrypt_wp hs) cfbEncrypt_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Proof.Cast5.cfbEncPost, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, cfb_sat⟩

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 cfbEncrypt)
      (Proof.Cast5.cfbEncryptRoundsContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Spec.Cast5.cfbPre X86.abi.ptrBits)
    (post := Proof.Cast5.cfbEncPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    cfbEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbEncPost_local _) (Proof.Cast5.cfbEncPostOut_local _) (cfb_frameSat _)

theorem cfbDecrypt_verified :
    Verified X86.target cfbDecrypt
      (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) (Proof.Cast5.cfbDecPost X86.abi.ptrBits)) :=
  cfbK_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Proof.Cast5.cfbDecPost, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, cfb_sat⟩

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 cfbDecrypt)
      (Proof.Cast5.cfbDecryptRoundsContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Spec.Cast5.cfbPre X86.abi.ptrBits)
    (post := Proof.Cast5.cfbDecPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbDecPost_local _) (Proof.Cast5.cfbDecPostOut_local _) (cfb_frameSat _)

/-! ## CBC -/

theorem cbcC_pre {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} (s : State)
    (h : (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s) :
    MPre true (s.withRegions (rdL true s) (wrL true s)) ∧ s.rd = [keyA s, tabA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrA s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch] at h
  obtain ⟨h4, hsp, hdrop, held, fitT, dTw, -, dTB, -, htake, hwr, dKV, dKD, dKS, -, dVD, dVS, dVA, dDS, dDA, dSA,
    -, dRV, dRD, dRS, -, dBK, dBV, dBD, dBS, -, fK, fV, fD, fS, nv⟩ := h
  have hrd : s.rd = [keyA s, tabA s] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop]; rfl
  have be : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
    simp only [below, VG.X86.Taint.sub_setWidth h4]
  have e8 : (arg s 4).toNat * 8 = 8 * (arg s 4).toNat := Nat.mul_comm _ _
  rw [e8] at hwr dKD dVD dDS dDA dRD dBD fD
  have mV : ivA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mD : dataA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mS : scrA s ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨⟨rfl, rfl, h4, (by show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega_using [hsp]), nv, fK, fV, fD, fS, fitT,
    (fun i hi => held i (by rw [s1234_length] at hi; exact hi)), dDS, dVS, (fun _ => dVD),
    (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dBK.symm),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dTB)⟩, hrd,
    (by rw [← e8] at hwr; exact hwr)⟩
  all_goals
    simp only [State.withRegions_wr, wrL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
  · exact dKD
  · exact dKV
  · exact dKS
  · exact dTw _ mD
  · exact dTw _ mV
  · exact dTw _ mS
  · exact dDA.symm
  · exact dVA.symm
  · exact dSA.symm
  · exact dRD
  · exact dRV
  · exact dRS
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBD
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBV
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBS

theorem cbcC_pub {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s₁)
    (_ : (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s₂)
    (h : (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeX true postX).pub (s₁.withRegions (rdL true s₁) (wrL true s₁))
      (s₂.withRegions (rdL true s₂) (wrL true s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
  obtain ⟨hsp, hsy, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hsp, fun i hi => ?_, hsy⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem cbcK_verified {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} {postX : State → State → Prop}
    {c : Prog isa}
    (hwp : ∀ s, (modeX true postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeX true postX).post s s')
    (hct : ConstantTime isa (modeX true postX).pre (modeX true postX).pub c)
    (hpost : ∀ s s', (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdL true s) (wrL true s)) (s'.withRegions (rdL true s) (wrL true s)) →
        (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeX true postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (cbcC_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdL true) (wrL true)
    (fun s h => (cbcC_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost cbcC_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := cbcC_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdL, wrL, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := cbcC_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrL, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem cbcC_sat {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} :
    (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre (satState true) := by
  have a0 : arg (satState true) 0 = 0x1000 := (sat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (satState true) 1 = 16 := (sat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (satState true) 2 = 0x2000 := (sat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (satState true) 3 = 0x3000 := (sat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (satState true) 4 = 0 := (sat_arg true 4 (by decide)).trans (by decide)
  have a5 : arg (satState true) 5 = 0x4000 := (sat_arg true 5 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : satState true = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch]
  subst s
  rw [a0, a1, a2, a3, a4, a5]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem cbcC_frameSat (post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cbcChainedSig.contract (X86.abi.withConsts ecbConsts) (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post true
      336).pre s := by
  refine ⟨frameSat true, ?_⟩
  have a0 : arg (frameSat true) 0 = 0x1000 := (frameSat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (frameSat true) 1 = 16 := (frameSat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (frameSat true) 2 = 0x2000 := (frameSat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (frameSat true) 3 = 0x3000 := (frameSat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (frameSat true) 4 = 0 := (frameSat_arg true 4 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : frameSat true = s
  sig_pre [Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  rw [a0, a1, a2, a3, a4]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained
      (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits)
        (Proof.Cast5.cbcEncChainedPost X86.abi.ptrBits)) :=
  cbcK_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcEncChainedPost,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, cbcC_sat⟩

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 cbcEncryptChained)
      (Proof.Cast5.cbcEncryptChainedRoundsContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcChainedSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Proof.Cast5.cbcChainedPre X86.abi.ptrBits)
    (post := Proof.Cast5.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cbcEncChainedPost_local _) (Proof.Cast5.cbcEncChainedPostOut_local _) (cbcC_frameSat _)

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained
      (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits)
        (Proof.Cast5.cbcDecChainedPost X86.abi.ptrBits)) :=
  cbcK_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcDecChainedPost,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, cbcC_sat⟩

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 cbcDecryptChained)
      (Proof.Cast5.cbcDecryptChainedRoundsContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcChainedSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Proof.Cast5.cbcChainedPre X86.abi.ptrBits)
    (post := Proof.Cast5.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cbcDecChainedPost_local _) (Proof.Cast5.cbcDecChainedPostOut_local _) (cbcC_frameSat _)

end VG.Proof.Cast5.X86.ModeFns
