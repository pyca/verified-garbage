module

public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.Cast5.X86.Modes
public import VerifiedGarbage.Proof.Cast5.ModeCipher
public import VerifiedGarbage.Proof.Cast5.X86.Block
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Cast5.X86.Ecb
import VerifiedGarbage.Proof.Framework.AddrArith

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
  rw [addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem argR_contains4 (s : State) : (argR s).Contains (addr (s.gpr .esp) 4) (32 / 8) := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem argR_contains8 {s : State} (h : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32) :
    (argR s).Contains (addr (s.gpr .esp) 8) (32 / 8) := by
  rw [addr8 h]; exact Offset.contains_base _ (by decide) (by decide)

/-- `Base` survives what keeps `esp`, the regions and the statics, and writes
memory apart from the arguments, the subkeys and the table. -/
theorem Base.frame {s s' : State} {K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} {rs : List Region}
    (h : Base s K k n) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (keyR K).Disjoint r ∧ (tabR s).Disjoint r ∧ (argR s).Disjoint r) : Base s' K k n := by
  have hA : ∀ r ∈ rs, (argR s).Disjoint r := fun r hr => (hd r hr).2.2
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
  exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega⟩

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

/-- The modes' data pointer and steps left (`4 dSlot`, `4 nSlot`), past the
working space and the block. -/
theorem modeSlots : 4 * dSlot = 280 ∧ 4 * nSlot = 284 := ⟨rfl, rfl⟩

theorem store_ok {s u : State} {S K D : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : BPre s S K D k n) (hu : RInv s S K k n lr u)
    (hW : InRegions s.wr (S.setWidth 64) 304) (hfit : S.toNat + 304 ≤ 2 ^ 32)
    (hDm : Region.Disjoint (blockR D) ⟨S.setWidth 64 + BitVec.ofNat 64 280, 8⟩) :
    WP isa (.block Modes.store) u (MPost s S D (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have c := hu.ctx
  have uD : u.mem.readW (addr S dataOff) 32 = D := by
    rw [slot_frame c.fitS hu.frame (fun r hr => (blockMem_disjoint h.ctx r hr).2.2) (by decide) (by decide)]
    exact h.dataSlot
  obtain ⟨X, hX⟩ : ∃ X, u.mem.readW (addr S 280) 32 = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, u.mem.readW (addr S 284) 32 = Y := ⟨_, rfl⟩
  have w0 : InRegions u.wr (addr D 0) 4 := by
    rw [addr_D0 h.fitD, hu.wr]
    obtain ⟨g, hg, hc⟩ := h.wD
    exact ⟨g, hg, by unfold Region.Contains at hc ⊢; omega⟩
  have w4 : InRegions u.wr (addr D 4) 4 := by
    rw [addr_off h.fitD 4 (by decide), hu.wr]
    exact CallLay.inRegions_sub h.wD (by omega) (by decide)
  have mW : ∀ e, e + 4 ≤ 304 → InRegions u.wr (addr S e) 4 := fun e he => by
    rw [addr_eq (by omega), hu.wr]; exact CallLay.inRegions_sub hW he (by decide)
  have mR : ∀ e, e + 4 ≤ 304 → InRegions (u.rd ++ u.wr) (addr S e) 4 := fun e he => by
    obtain ⟨g, hg, hc⟩ := mW e he; exact ⟨g, List.mem_append_right _ hg, hc⟩
  have rdD := mR dataOff (by decide)
  have rdX := mR 280 (by decide)
  have rdY := mR 284 (by decide)
  have wX := mW 280 (by decide)
  have wY := mW 284 (by decide)
  have hbx := hu.bx
  have hbp := hu.bp
  obtain ⟨m', hm'⟩ : ∃ m', (u.mem.writeW (addr D 0) (byteRev32 lr.2)).writeW (addr D 4) (byteRev32 lr.1) = m' :=
    ⟨_, rfl⟩
  have sm (e : Nat) (h1 : 280 ≤ e) (h2 : e + 4 ≤ 288) : m'.readW (addr S e) 32 = u.mem.readW (addr S e) 32 := by
    have hs (o : Nat) (ho : o + 4 ≤ 8) : Mem.Sep (addr S e) 4 (addr D o) 4 := by
      refine Region.Disjoint.sep hDm.symm ?_ ?_
      · rw [addr_eq (by omega)]; exact Offset.contains _ h1 (by omega) (by omega)
      · rw [addr_off h.fitD o (by omega)]; exact Offset.contains_base _ (by omega) (by omega)
    rw [← hm', Mem.readW_writeW_sep (w' := 32) (hs 4 (by decide)) (by decide),
      Mem.readW_writeW_sep (w' := 32) (hs 0 (by decide)) (by decide)]
  have e : (m'.writeW (addr S 280) X).writeW (addr S 284) Y = m' := by
    rw [← hX, ← sm 280 (by decide) (by decide), writeW_readW, ← hY, ← sm 284 (by decide) (by decide),
      writeW_readW]
  unfold Modes.store
  refine wp_ldm (b := .esi) (B := S) (o := dataOff) c.si rdD fun u₁ v₁ => ?_
  have si₁ : u₁.gpr .esi = S := (v₁.other _ (by decide)).trans c.si
  refine wp_ldm (b := .esi) (B := S) (o := 4 * dSlot) si₁ (by rw [v₁.rd, v₁.wr]; exact rdX) fun u₂ v₂ => ?_
  have si₂ : u₂.gpr .esi = S := (v₂.other _ (by decide)).trans si₁
  refine wp_ldm (b := .esi) (B := S) (o := 4 * nSlot) si₂ (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr]; exact rdY)
    fun u₃ v₃ => ?_
  refine wp_bswap fun u₄ v₄ => ?_
  have dx₄ : u₄.gpr .edx = D := by
    rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, uD]
  refine wp_stm (b := .edx) (B := D) (o := 0) dx₄ (by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact w0) fun u₅ v₅ => ?_
  refine wp_bswap fun u₆ v₆ => ?_
  refine wp_stm (b := .edx) (B := D) (o := 4) (by rw [v₆.other _ (by decide), v₅.gpr]; exact dx₄)
    (by rw [v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact w4) fun u₇ v₇ => ?_
  have si₆ : u₆.gpr .esi = S := by
    rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide)]; exact si₂
  refine wp_stm (b := .esi) (B := S) (o := 4 * dSlot) (by rw [v₇.gpr]; exact si₆)
    (by rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact wX) fun u₈ v₈ => ?_
  refine wp_stm (b := .esi) (B := S) (o := 4 * nSlot) (by rw [v₈.gpr, v₇.gpr]; exact si₆)
    (by rw [v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact wY) fun u₉ v₉ => ?_
  refine wp_mov fun u₁₀ v₁₀ => WP.block_nil ?_
  have g₉ : ∀ r, u₉.gpr r = u₆.gpr r := fun r => by rw [v₉.gpr, v₈.gpr, v₇.gpr]
  have bp₄ : u₄.gpr .ebp = byteRev32 lr.2 := by
    rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hbp]; rfl
  have bx₆ : u₆.gpr .ebx = byteRev32 lr.1 := by
    rw [v₆.gpr, v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), hbx]; rfl
  have ax₆ : u₆.gpr .eax = X := by
    rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem]; exact hX
  have cx₆ : u₆.gpr .ecx = Y := by
    rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem]; exact hY
  have m₁₀ : u₁₀.mem = m' := by
    rw [v₁₀.mem, v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    simp only [v₈.gpr, v₇.gpr, ax₆, cx₆, bx₆, bp₄]
    rw [show 4 * dSlot = 280 from rfl, show 4 * nSlot = 284 from rfl, hm', e]
  refine ⟨?_, ?_, ?_, fun q hq => ?_, by rw [v₁₀.rd, v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hu.rd],
    by rw [v₁₀.wr, v₉.wr, v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, hu.wr],
    by rw [v₁₀.syms, v₉.syms, v₈.syms, v₇.syms, v₆.syms, v₅.syms, v₄.syms, v₃.syms, v₂.syms, v₁.syms, hu.syms]⟩
  · rw [m₁₀, ← hm', addr_D0 h.fitD, addr_off h.fitD 4 (by decide), blockAt_write]
  · rw [m₁₀, ← hm']
    have c0 : (blockR D).Contains (addr D 0) (32 / 8) := by
      rw [addr_D0 h.fitD]; simp [Region.Contains]
    have c4 : (blockR D).Contains (addr D 4) (32 / 8) := by
      rw [addr_off h.fitD 4 (by decide)]; exact Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by decide) (by decide)
    have f1 := (hu.frame.mono (rs' := blockR D :: blockMem S (s.gpr .esp))
      (fun r hr => List.mem_cons_of_mem _ hr)).writeW List.mem_cons_self (byteRev32 lr.2) c0
    exact f1.writeW List.mem_cons_self (byteRev32 lr.1) c4
  · rw [v₁₀.gpr, g₉]; exact si₆
  · have a : q ≠ .edx := fun e => hq (by rw [e]; decide)
    have b : q ≠ .eax := fun e => hq (by rw [e]; decide)
    have d : q ≠ .ecx := fun e => hq (by rw [e]; decide)
    have f : q ≠ .edi := fun e => hq (by rw [e]; decide)
    have g : q ≠ .ebx := fun e => hq (by rw [e]; decide)
    have i : q ≠ .ebp := fun e => hq (by rw [e]; decide)
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
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt h]

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
  have aE4 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := inRegions_prefix hb.inA (by decide)
  have aE8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := by
    rw [addr8 hb.fitE]; exact CallLay.inRegions_sub hb.inA (by decide) (by decide)
  have aB : ∀ e, e < 4 * 76 → addr B e = B.setWidth 64 + BitVec.ofNat 64 e := fun e he => addr_eq (by omega)
  have sW : ∀ e, e + 4 ≤ 4 * 76 → InRegions s.wr (addr B e) 4 := fun e he => by
    rw [aB e (by omega)]; exact ⟨_, hw, Offset.contains_base _ he (by omega)⟩
  -- The slots `48 … 59` of the working space.
  have inSl : ∀ e, 48 ≤ e → e + 4 ≤ 60 → (⟨B.setWidth 64, 4 * 66⟩ : Region).Contains (addr B e) (32 / 8) :=
    fun e h1 h2 => by rw [aB e (by omega)]; exact Offset.contains_base _ (by omega) (by omega)
  show WP isa (.seq (.block Modes.setup) (.seq (.block load)
    (.seq (if up then encryptBlock else decryptBlock) (.block Modes.store)))) s _
  refine WP.seq ?_
  refine wp_mov fun s₁ u₁ => ?_
  refine wp_ldm (b := .esp) (B := s.gpr .esp) (o := 4) (u₁.other _ (by decide)) (by rw [u₁.rd, u₁.wr]; exact aE4)
    fun s₂ u₂ => ?_
  have si₂ : s₂.gpr .esi = B := by rw [u₂.other _ (by decide), u₁.gpr]; exact hB'
  refine wp_stm (b := .esi) (B := B) (o := schedOff) si₂ (by rw [u₂.wr, u₁.wr]; exact sW _ (by decide))
    fun s₃ u₃ => ?_
  refine wp_ldm (b := .esp) (B := s.gpr .esp) (o := 8)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact aE8) fun s₄ u₄ => ?_
  have si₄ : s₄.gpr .esi = B := by rw [u₄.other _ (by decide), u₃.gpr]; exact si₂
  refine wp_stm (b := .esi) (B := B) (o := roundsOff) si₄ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sW _ (by decide))
    fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => ?_
  have si₇ : s₇.gpr .esi = B := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; exact si₄
  refine wp_stm (b := .esi) (B := B) (o := dataOff) si₇
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sW _ (by decide)) fun s₈ u₈ => WP.block_nil ?_
  -- The state after the setup.
  have esp₈ : s₈.gpr .esp = s.gpr .esp := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  have rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sy₈ : s₈.syms = s.syms := by
    rw [u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  have si₈ : s₈.gpr .esi = B := by rw [u₈.gpr]; exact si₇
  have edi₈ : s₈.gpr .edi = B := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB'
  have ax₂ : s₂.gpr .eax = K := by rw [u₂.gpr, u₁.mem]; exact hb.argK
  have sepA : ∀ e, 48 ≤ e → e + 4 ≤ 60 → Mem.Sep (addr (s.gpr .esp) 8) 4 (addr B e) 4 := fun e h1 h2 =>
    Region.Disjoint.sep dAB (argR_contains8 hb.fitE) (by rw [aB e (by omega)]; exact Offset.contains_base _ (by omega) (by omega))
  have ax₄ : s₄.gpr .eax = BitVec.ofNat 32 n := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, ax₂, Mem.readW_writeW_sep (w' := 32) (sepA schedOff (by decide) (by decide)) (by decide)]
    exact hb.argN
  have ax₇ : s₇.gpr .eax = B + BitVec.ofNat 32 256 := by rw [u₇.gpr, u₆.gpr, u₅.gpr, si₄]; rfl
  have m₈ : s₈.mem = ((s.mem.writeW (addr B schedOff) K).writeW (addr B roundsOff) (BitVec.ofNat 32 n)).writeW
      (addr B dataOff) (B + BitVec.ofNat 32 256) := by
    rw [u₈.mem, ax₇, u₇.mem, u₆.mem, u₅.mem, ax₄, u₄.mem, u₃.mem, ax₂, u₂.mem, u₁.mem]
  -- The setup writes the slots `48 … 59` only.
  have slR : Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩ ⟨B.setWidth 64, 4 * 66⟩ :=
    Offset.sub_base _ (by decide)
  have inSl' : ∀ e, 48 ≤ e → e + 4 ≤ 60 →
      (⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩ : Region).Contains (addr B e) (32 / 8) :=
    fun e h1 h2 => by rw [aB e (by omega)]; exact Offset.contains _ h1 (by omega) (by omega)
  have f₈ : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩] s.mem s₈.mem := by
    rw [m₈]
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (inSl' 48 (by decide) (by decide))).writeW
      List.mem_cons_self _ (inSl' 52 (by decide) (by decide))).writeW List.mem_cons_self _
      (inSl' 56 (by decide) (by decide))
  have coreScr : Region.Sub ⟨B.setWidth 64, 4 * 66⟩ ⟨B.setWidth 64, 4 * 76⟩ := Region.sub_prefix (by decide)
  have slScr : Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩ ⟨B.setWidth 64, 4 * 76⟩ :=
    Offset.sub_base _ (by decide)
  have dSl : ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩ : Region)], (keyR K).Disjoint r ∧
      (tabR s).Disjoint r ∧ (argR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨dKB.sub_right slScr, dTB.sub_right slScr, dAB.sub_right slScr⟩
  have hb₈ : Base s₈ K k n := hb.frame esp₈ rd₈ wr₈ sy₈ f₈ dSl
  have sep48 : ∀ d e, d + 4 ≤ e ∨ e + 4 ≤ d → d < 256 → e < 256 → Mem.Sep (addr B d) 4 (addr B e) 4 :=
    fun d e h hd he => slot_sep (by omega) hd he h (by decide) (by decide)
  have rB : Region.Sub ⟨B.setWidth 64, 256⟩ ⟨B.setWidth 64, 4 * 76⟩ := Region.sub_prefix (by decide)
  have eD : (B + BitVec.ofNat 32 256).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 256 := aB 256 (by decide)
  have blkSub : Region.Sub (blockR (B + BitVec.ofNat 32 256)) ⟨B.setWidth 64, 4 * 66⟩ := by
    show Region.Sub ⟨(B + BitVec.ofNat 32 256).setWidth 64, 8⟩ _
    rw [eD]; exact Offset.sub_base _ (by decide)
  have hpre : BPre s₈ B K (B + BitVec.ofNat 32 256) k n := by
    refine ⟨⟨si₈, by omega, ?_, ?_, ?_, hb.nv, hb.fitK, hb₈.inK, fun j hj => ?_, by rw [esp₈]; exact hb.sp,
      by rw [esp₈]; exact (hsd.sub_right rB).symm, hb₈.dKs, dKB.sub_right rB, hb₈.fitT, hb₈.inT, hb₈.dTs,
      by rw [sy₈]; exact dTB.sub_right rB, tabAt_of_held hb₈.held⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [wr₈]; exact ⟨_, hw, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
    · rw [m₈, Mem.readW_writeW_sep (w' := 32) (sep48 48 56 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (w' := 32) (sep48 48 52 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32]
    · rw [m₈, Mem.readW_writeW_sep (w' := 32) (sep48 52 56 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32]
    · rw [← Proof.Cast5.scheduleAt_getD _ _ hj, hb₈.sk]
    · rw [m₈, Mem.readW_writeW_self32]
    · rw [toNat_add32 (by omega)]; omega
    · rw [wr₈, eD]; exact ⟨_, hw, Offset.contains_base _ (by decide) (by omega)⟩
    · show Region.Disjoint ⟨(B + BitVec.ofNat 32 256).setWidth 64, 8⟩ _
      rw [eD]; exact Offset.disjoint_base _ (by decide) (by omega)
    · exact ((dKB.sub_right coreScr).sub_right blkSub).symm
    · rw [sy₈]; exact ((dTB.sub_right coreScr).sub_right blkSub).symm
    · rw [esp₈]; exact ((hsd.sub_right coreScr).sub_right blkSub).symm
  refine WP.seq (WP.mono (load_ok hpre) fun u₉ ⟨c₉, hlr, m₉, g₉, rd₉, wr₉, sy₉⟩ => ?_)
  have esp₉ : u₉.gpr .esp = s.gpr .esp := (g₉ .esp (by decide)).trans esp₈
  have hb₉ : BPre u₉ B K (B + BitVec.ofNat 32 256) k n := ⟨c₉, by rw [m₉]; exact hpre.dataSlot, hpre.fitD,
    by rw [wr₉]; exact hpre.wD, hpre.dDS, hpre.dDK, by rw [sy₉]; exact hpre.dDT,
    by rw [esp₉, ← esp₈]; exact hpre.dDsp⟩
  obtain ⟨lr, hlr'⟩ : ∃ lr, Spec.Cast5.decodeBlock
      (Spec.Cast5.blockAt s₈.mem ((B + BitVec.ofNat 32 256).setWidth 64)) = lr := ⟨_, rfl⟩
  rw [hlr'] at hlr
  have hbx : u₉.gpr .ebx = lr.1 := by rw [← hlr]
  have hbp : u₉.gpr .ebp = lr.2 := by rw [← hlr]
  have hW₉ : InRegions u₉.wr (B.setWidth 64) 304 := by
    rw [wr₉, wr₈]; exact ⟨_, hw, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  have hDm : (blockR (B + BitVec.ofNat 32 256)).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 280, 8⟩ := by
    show Region.Disjoint ⟨(B + BitVec.ofNat 32 256).setWidth 64, 8⟩ _
    rw [eD]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have hsm : (below (u₉.gpr .esp) 4).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 280, 8⟩ := by
    rw [esp₉]; exact hsd.sub_right (Offset.sub_base _ (by decide))
  have stkEq : stkRegion (s.gpr .esp) (dirCore up).stack = below (s.gpr .esp) 4 := rfl
  have post (v : State) (hv : RInv u₉ B K k n (fold up k n lr) v) :
      WP isa (.block Modes.store) v fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
        Ready s' B (k, n) ∧
        Frame [coreRegion (dirCore up) B, stkRegion (s.gpr .esp) (dirCore up).stack] s.mem s'.mem ∧
        (∀ j < (dirCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw) =
          dirCipher up (k, n).1 (k, n).2 (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw))) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine WP.mono (store_ok hb₉ hv hW₉ (by omega) hDm) fun w hw' => ?_
    have espw : w.gpr .esp = s.gpr .esp := (hw'.same .esp (by decide)).trans esp₉
    have fall : Frame [coreRegion (dirCore up) B, stkRegion (s.gpr .esp) (dirCore up).stack] s.mem w.mem := by
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
    have dAll : ∀ r ∈ [coreRegion (dirCore up) B, stkRegion (s.gpr .esp) (dirCore up).stack],
        (keyR K).Disjoint r ∧ (tabR s).Disjoint r ∧ (argR s).Disjoint r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dKB.sub_right coreScr, dTB.sub_right coreScr, dAB.sub_right coreScr⟩
      · exact ⟨hb.dKs, hb.dTs, hb.dAs⟩
    refine ⟨hw'.edi, espw, ⟨K, hb.frame espw (hw'.rd.trans (rd₉.trans rd₈)) (hw'.wr.trans (wr₉.trans wr₈))
      (hw'.syms.trans (sy₉.trans sy₈)) fall dAll, by simp only [stk, espw]; exact hsd⟩, fall, fun j hj => ?_,
      hw'.rd.trans (rd₉.trans rd₈), hw'.wr.trans (wr₉.trans wr₈)⟩
    have hj0 : j = 0 := by simp only [dirCore] at hj; omega
    subst hj0
    have eB : blkAddr (dirCore up) B 0 = B.setWidth 64 + BitVec.ofNat 64 256 := by
      simp [blkAddr, slotA, dirCore, bufSlot]
    have dBlk : ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 48, 12⟩ : Region)],
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
