module

import VerifiedGarbage.Proof.TripleDes.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.Fb
public import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Proof.Modes.Cfb8
public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.TripleDes.X86_64.BlockSum
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.Fb
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.TripleDes.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Modes.X86_64.Fb
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Spec.TripleDes.Cfb
meta import VerifiedGarbage.Proof.Modes.Cfb8
meta import VerifiedGarbage.Proof.Modes.Fb
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BlockSum
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Fb
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.TripleDes.X86_64.ConstantTime
public import VerifiedGarbage.Impl.Modes.X86_64.Cfb8
public import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Steps
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Modes.X86_64.Ctr
import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
meta import VerifiedGarbage.Impl.Modes.X86_64.Cfb8
meta import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
meta import VerifiedGarbage.Proof.Modes.X86_64.Setup
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Steps
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Modes.X86_64.Words
meta import VerifiedGarbage.Proof.Modes.X86_64.Steps
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.Modes.X86_64.Ctr
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
public import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Spec.TripleDes.Cbc
meta import VerifiedGarbage.Spec.Weierstrass

/-! ### `TripleDes.X86_64.CallPatch`, which this module and modules that import it used -/

section

/-!
# Triple DES's modes on x86-64: the call's return address

The modes call the block function, whose return address the call stores
below the stack pointer (`hole`), which no buffer of the modes overlaps
(`Clear`): what the modes' contracts say of the data and the IV holds of the
memory with that hole patched (`Verified.of_inline_ct`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64

theorem patch_mem {H : Region} {b : State} {hv : Mem} {u : Nat → BitVec 64} {p : Addr} {n : Nat}
    (hb : ∀ i < n, ¬ H.Contains (p + BitVec.ofNat 64 i) 1) :
    ∀ i < n, (b.patch H hv u).mem (p + BitVec.ofNat 64 i) = b.mem (p + BitVec.ofNat 64 i) :=
  fun i hi => by simp only [State.patch, overlay, hb i hi, ite_false]

theorem bytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = m' (p + BitVec.ofNat 64 i)) :
    Spec.TripleDes.bytesAt m p n = Spec.TripleDes.bytesAt m' p n := by
  simp only [Spec.TripleDes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem cbcBlocksAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < 8 * n, m (p + BitVec.ofNat 64 i) = m' (p + BitVec.ofNat 64 i)) :
    Spec.TripleDes.cbcBlocksAt m p n = Spec.TripleDes.cbcBlocksAt m' p n := by
  simp only [Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [Function.comp_apply, Spec.TripleDes.blockAt]
  refine congrArg Vector.toList (congrArg Vector.ofFn (funext fun j => ?_))
  rw [Offset.add_add]
  exact h _ (by have := j.isLt; omega_using [hi])

end VG.Proof.TripleDes.X86_64

end

end

/-! ### `Modes.X86_64.Cfb8`, which only this module used -/

section

/-! ### `Modes.X86_64.Cfb8Loop`, which only this module used -/

section

/-!
# CFB8 on x86-64, for any core: the data loop

`cfb8Block_wp`: one iteration copies the input block `Iⱼ` from the IV to
the buffer (`copyN_wp`), enciphers it there (`BlockSpec.crypt_wp`), XORs
the output's first byte into byte `j` of the data (`cfb8Xor_wp`), making it
`cfb8Out`, and shifts the input block at the IV to `Iⱼ₊₁` (`cfb8Shift_wp`,
`cfb8In`). Blocks are `8 bw` bytes.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeW8_apply)

variable {c : Core}

/-- What CFB8's data loop works on: the scratch buffer at `B`, the `n`
bytes at `D`, the input block at `P`, whose address is in `ivX`. -/
structure C8Pre (c : Core) (s₀ : State) (B D P : Addr) (n : Nat) : Prop where
  scr : ScrIn s₀ B c.ctrSlots
  dat : (⟨D, n⟩ : Region) ∈ s₀.wr
  ivw : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr
  sepD : Region.Disjoint ⟨D, n⟩ ⟨B, 8 * c.ctrSlots⟩
  sepP : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩
  sepPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, n⟩
  fitD : D.toNat + n ≤ 2 ^ 64
  small : n < 2 ^ 64
  ivx : s₀.xmm Core.ivX = (0 : BitVec 64) ++ P
  stk : StkOk c s₀

/-- The data loop, before byte `j`; `m₀` is the memory on entry, `iv` the
IV. -/
structure C8Inv (cs : BlockSpec c) (enc : Bool) (s₀ : State) (m₀ : Mem) (B D P : Addr) (n : Nat) (k : cs.Key)
    (iv : List Byte) (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s B k
  saved : ∀ i < 7, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 j
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - j)
  lt : j < n
  ivB : ∀ u < 8 * c.bw, s.mem (P + BitVec.ofNat 64 u) = (cfb8In enc (cs.cipher k) m₀ D iv j).getD u 0
  data : ∀ q < n, s.mem (D + BitVec.ofNat 64 q) =
    if q < j then cfb8Out enc (cs.cipher k) m₀ D iv q else m₀ (D + BitVec.ofNat 64 q)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm Core.ivX = s₀.xmm Core.ivX

/-- The data loop, done. -/
structure C8Done (cs : BlockSpec c) (enc : Bool) (s₀ : State) (m₀ : Mem) (B D P : Addr) (n : Nat) (k : cs.Key)
    (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 7, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  ivB : ∀ u < 8 * c.bw, s.mem (P + BitVec.ofNat 64 u) = (cfb8In enc (cs.cipher k) m₀ D iv n).getD u 0
  data : ∀ q < n, s.mem (D + BitVec.ofNat 64 q) = cfb8Out enc (cs.cipher k) m₀ D iv q
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm Core.ivX = s₀.xmm Core.ivX

theorem headD_eq_getD (l : List Byte) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

theorem writeW8_frame (m : Mem) (A : Addr) (b : Byte) : Frame [⟨A, 1⟩] m (m.writeW A b) := fun x hx => by
  rw [writeW8_apply, ite_eq_right (fun h => hx _ List.mem_cons_self (by
    subst h; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []))]

theorem cfb8Block_wp (cs : BlockSpec c) (enc : Bool) {s₀ : State} {m₀ : Mem} {B D P : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : C8Pre c s₀ B D P n) (hsc : KeepsIv c.crypt)
    {j : Nat} {s : State} (hi : C8Inv cs enc s₀ m₀ B D P n k iv j s) :
    WP isa (c.cfb8Block enc) s fun s' => (s'.zf = some true ∧ C8Done cs enc s₀ m₀ B D P n k iv s') ∨
      (s'.zf = some false ∧ C8Inv cs enc s₀ m₀ B D P n k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hn64 := hp.small
  have hj := hi.lt
  obtain hL0 : 0 < 8 * c.bw := by omega_arith
  obtain hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, -, dc, dbp, -, dsb, dsp, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, -, lc, lbp, -, lsb, lsp, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_arith
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 j
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  let S : Region := ⟨B, 8 * c.ctrSlots⟩
  obtain hwS : S ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  obtain hwD : (⟨D, n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.ivw
  obtain subT : Region.Sub ⟨T, 8 * c.bw⟩ S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  obtain subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  obtain subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith)
  obtain subA : Region.Sub ⟨A, 1⟩ ⟨D, n⟩ := VG.Offset.sub_base D (by omega_arith)
  obtain dTP : Region.Disjoint ⟨T, 8 * c.bw⟩ ⟨P, 8 * c.bw⟩ := (hp.sepP.sub_right subT).symm
  obtain dAP : Region.Disjoint ⟨A, 1⟩ ⟨P, 8 * c.bw⟩ := (hp.sepPD.sub_right subA).symm
  obtain dAS : Region.Disjoint ⟨A, 1⟩ S := hp.sepD.sub_left subA
  obtain dPcore : Region.Disjoint ⟨P, 8 * c.bw⟩ (coreRegion c B) := hp.sepP.sub_right subCore
  obtain dDcore : Region.Disjoint ⟨D, n⟩ (coreRegion c B) := hp.sepD.sub_right subCore
  obtain inS : ∀ {d m : Nat}, d + m ≤ 8 * c.ctrSlots → InRegions s.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hwS, VG.Offset.contains_base B h (by omega_arith)⟩
  obtain inA : InRegions s.wr A 1 := ⟨_, hwD, VG.Offset.contains_base D (by omega_arith) (by omega_arith)⟩
  obtain slotIn : ∀ i < 7, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  obtain slotOut : ∀ i < 7, ∀ {R : Region}, (R = ⟨T, 8 * c.bw⟩ ∨ R = coreRegion c B ∨ R = ⟨A, 1⟩ ∨
      R = ⟨P, 8 * c.bw⟩) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi7 R hR => by
    rcases hR with rfl | rfl | rfl | rfl
    · exact VG.Offset.disjoint B (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)
    · exact (dAS.sub_right (slotIn i hi7)).symm
    · exact (hp.sepP.sub_right (slotIn i hi7)).symm
  obtain px : s.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [hi.xmm, hp.ivx]
  -- The input block to the buffer.
  unfold Core.cfb8Block
  obtain ⟨s₁a, e₁a, ax₁a, o₁a, m₁a, rd₁a, wr₁a, x₁a⟩ := movqR_ok s .rax Core.ivX
  obtain ax₁ : s₁a.gpr .rax = P := by rw [ax₁a, px, extract_zero_append]
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁a, e₁a, WP.mono_syms (WP.vecKeep
    (c := .block ((List.range c.bw).flatMap (copyW .rbp sb .rax (8 * c.buf) 0)))
    (flatMap_scal (copyW_scal _ _ _ _ _) _) (copyN_wp (k := c.bw)
    (t := .rbp) (rd := sb) (rs := .rax) (od := 8 * c.buf) (os := 0) (P := T) (Q := P)
    ⟨by rw [o₁a _ (by decide), hi.base], by rw [ax₁]; simp, by decide, by decide,
      fun w hw => by rw [wr₁a, addr_add]; exact inS (by simp only [Core.ctrSlots]; omega_arith),
      fun w hw => by rw [rd₁a, wr₁a]; exact inRd ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
      dTP, by omega_arith⟩)) fun s₁ ⟨h₁, x₁, _⟩ sy₁ => ?_⟩))
  obtain mem₁ : s₁.mem = over s.mem T (8 * c.bw) fun i => s.mem (P + BitVec.ofNat 64 i) := by rw [h₁.mem, m₁a]
  obtain f₁ : Frame [⟨T, 8 * c.bw⟩] s.mem s₁.mem := by rw [mem₁]; exact over_frame _ _ _ _
  obtain g₁ : ∀ x, x ≠ .rax → x ≠ .rbp → s₁.gpr x = s.gpr x := fun x h1 h2 => by rw [h₁.regs x h2, o₁a x h1]
  obtain base₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide) (by decide), hi.base]
  obtain ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr subTbuf)
    ⟨fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, hwS, subT⟩,
      by rw [h₁.rd, rd₁a], by rw [h₁.wr, wr₁a], by rw [sy₁, runBlock_syms e₁a]⟩ fun r hr => by
    obtain ⟨h1, -, -, h4, -, -, -⟩ := of_not_modeRegs hr; exact g₁ r h1 h4
  obtain rd₁ : s₁.rd = s₀.rd := by rw [h₁.rd, rd₁a, hi.rd]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [h₁.wr, wr₁a, hi.wr]
  -- Enciphered.
  refine WP.seq (WP.mono (WP.keepIv hsc (by rw [x₁, x₁a, px]; exact hi_zero_append _) (cs.crypt_wp base₁ ⟨by rw [wr₁]; exact hp.scr.wr, hfit⟩ ready₁))
    fun s₂ ⟨⟨base₂, rsp₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩, x₂⟩ => ?_)
  rw [show s₁.gpr .rsp = s₀.gpr .rsp by rw [g₁ _ (by decide) (by decide), hi.rsp]] at f₂
  obtain eT : blkAddr c B 0 = T := by simp only [blkAddr, T, Nat.mul_zero, Nat.add_zero]
  obtain hX : bytesAt s₁.mem T (8 * c.bw) = cfb8In enc ciph m₀ D iv j := by
    apply List.ext_getElem (by
      simp only [bytesAt, List.length_map, List.length_range]; rw [cfb8In_length enc ciph m₀ D hiv hL0])
    intro u h1 _
    obtain hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [mem₁, over_at hu (by omega_arith), hi.ivB u hu, List.getElem_eq_getD 0]
  obtain T₂ : s₂.mem T = (ciph (cfb8In enc ciph m₀ D iv j)).headD 0 := by
    obtain h0 : s₂.mem T = (bytesAt s₂.mem T (8 * c.bw)).getD 0 0 := by rw [bytesAt_getD _ _ hL0]; simp
    rw [h0, ← eT, ks₂ 0 hG0, eT, hX, headD_eq_getD]
  -- The memory outside the buffer and the core, as before.
  obtain out₂ : ∀ x, (∀ R ∈ [(⟨T, 8 * c.bw⟩ : Region), coreRegion c B], ¬ R.Contains x 1) →
      (∀ R ∈ stkList c (s₀.gpr .rsp), ¬ R.Contains x 1) → s₂.mem x = s.mem x :=
    fun x hx hs => by
      rw [f₂ x (fun R hR => by
          rcases List.mem_cons.mp hR with rfl | hR
          · exact hx _ (by simp)
          · exact hs R hR),
        f₁ x (fun R hR => hx R (by simp only [List.mem_singleton] at hR; subst hR; simp))]
  obtain A₂ : s₂.mem A = m₀ A := by
    rw [out₂ A (fun R hR hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact (dAS.sub_right subT) A (Region.contains_self A 1) hc
      · exact (dAS.sub_right subCore) A (Region.contains_self A 1) hc)
      (fun R hR hc => hp.stk.disj ⟨_, hp.dat, subA⟩ R hR A (Region.contains_self A 1) hc)]
    have := hi.data j hj
    rw [ite_eq_right (Nat.lt_irrefl _)] at this
    exact this
  obtain data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, g₁ _ da dbp, hi.dataR]
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  obtain px₂ : s₂.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [x₂, x₁, x₁a, px]
  -- The byte, and the shift.
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono_syms (WP.vecKeep (by cases enc <;> rfl)
    (cfb8Xor_wp enc (s := s₂) (A := A) (T := T) data₂ (by rw [base₂]) da dbp
    (by rw [wr₂', ← hi.wr]; exact inA)
    (by rw [rd₂', wr₂', ← hi.rd, ← hi.wr]; exact inRd (inS (by simp only [Core.ctrSlots]; omega_arith)))))
    fun s₃ ⟨⟨g₃, rd₃, wr₃, m₃, ax₃⟩, x₃, _⟩ sy₃ => ?_)))
  obtain ⟨sK, eK, cK, oK, mK, rdK, wrK, xK⟩ := movqR_ok s₃ .rcx Core.ivX
  refine WP.of_runBlock ⟨sK, eK, WP.mono_syms (WP.vecKeep (c := .block c.cfb8Shift)
    (by simp only [scalCode, Core.cfb8Shift, List.all_append, Bool.and_eq_true]
        exact ⟨flatMap_scal (fun _ => rfl) _, rfl⟩)
    (cfb8Shift_wp (s := sK) (P := P) (by rw [cK, x₃, px₂, extract_zero_append])
      (by rw [wrK, wr₃, wr₂']; exact hp.ivw) hbw0 hbw2))
    fun s₄ ⟨⟨g₄s, rd₄s, wr₄s, P₄, f₄⟩, x₄, _⟩ sy₄ => ?_⟩
  obtain cj : (s₃.gpr .rax).setWidth 8 = cfb8C enc ciph m₀ D iv j := by
    rw [ax₃, A₂, T₂]; rfl
  rw [oK _ (by decide), cj, mK] at P₄
  rw [mK] at f₄
  obtain g₄ : ∀ x, x ≠ .rcx → x ≠ .rbp → s₄.gpr x = s₃.gpr x := fun x h1 h2 => by rw [g₄s x h2, oK x h1]
  obtain rd₄ : s₄.rd = s₃.rd := by rw [rd₄s, rdK]
  obtain wr₄ : s₄.wr = s₃.wr := by rw [wr₄s, wrK]
  -- On to the next byte.
  obtain ⟨s₅a, e₅a, a₅a, o₅a, m₅a, rd₅a, wr₅a⟩ := addImm_ok s₄ c.dataReg 1
  obtain ⟨s₅, e₅, l₅, z₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₅a c.leftReg 1
  refine WP.of_runBlock ⟨s₅, by
    rw [Core.cfb8Next, show ([.alu .add c.dataReg (.imm 1), .alu .sub c.leftReg (.imm 1)] : List Instr) =
      [.alu .add c.dataReg (.imm 1)] ++ [.alu .sub c.leftReg (.imm 1)] from rfl, runBlock_app, e₅a, Option.bind_some,
      e₅], ?_⟩
  obtain keep₅ : ∀ x, x ≠ .rax → x ≠ .rbp → x ≠ .rcx → x ≠ c.dataReg → x ≠ c.leftReg → s₅.gpr x = s₂.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [o₅ x h5, o₅a x h4, g₄ x h3 h2, g₃ x h1 h2]
  obtain left₄ : s₅a.gpr c.leftReg = BitVec.ofNat 64 (n - j) := by
    rw [o₅a _ (Ne.symm hdl), g₄ _ lc lbp, g₃ _ la lbp, lr₂, g₁ _ la lbp, hi.leftR]
  obtain left₅ : s₅.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [l₅, left₄, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show n - j - 1 = n - (j + 1) by omega_arith]
  obtain hz₅ : s₅.zf = some (decide (j + 1 = n)) := by
    rw [z₅, left₄, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_arith
  obtain data₅ : s₅.gpr c.dataReg = D + BitVec.ofNat 64 (j + 1) := by
    rw [o₅ _ hdl, a₅a, g₄ _ dc dbp, g₃ _ da dbp, data₂,
      show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, addr_add]
  obtain mem₅ : s₅.mem = s₄.mem := by rw [m₅, m₅a]
  obtain xmm₅ : s₅.xmm Core.ivX = s₀.xmm Core.ivX := by
    rw [runBlock_vec rfl e₅, runBlock_vec rfl e₅a, x₄, xK, x₃, x₂, x₁, x₁a, hi.xmm]
  obtain base₅ : s₅.gpr sb = B := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂]
  obtain rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp), rsp₂, g₁ _ (by decide) (by decide),
      hi.rsp]
  obtain rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₅a, rd₄, rd₃, rd₂']
  obtain wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₅a, wr₄, wr₃, wr₂']
  -- What changed after `crypt`: the data's byte and the input block.
  obtain f₅ : Frame [⟨A, 1⟩, ⟨P, 8 * c.bw⟩] s₂.mem s₅.mem := by
    rw [mem₅]
    refine (?_ : Frame [⟨A, 1⟩, ⟨P, 8 * c.bw⟩] s₂.mem s₃.mem).trans
      (f₄.mono fun R hR => by simp only [List.mem_singleton] at hR; subst hR; simp)
    rw [m₃]; exact (writeW8_frame _ _ _).mono fun R hR => by simp only [List.mem_singleton] at hR; subst hR; simp
  obtain ready₅ : cs.Ready s₅ B k := cs.ready_frame ready₂ f₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (dDcore.sub_left subA).symm
    · exact .inl dPcore.symm)
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by rw [wr₂, wr₁, ← hi.wr]; exact hwD, subA⟩
      · exact ⟨_, by rw [wr₂, wr₁, ← hi.wr]; exact hwP, fun _ h => h⟩,
      by rw [rd₅, rd₅a, rd₄, rd₃], by rw [wr₅, wr₅a, wr₄, wr₃],
      by rw [runBlock_syms e₅, runBlock_syms e₅a, sy₄, runBlock_syms eK, sy₃]⟩ fun r hr => by
    obtain ⟨h1, -, h3, h4, -, h6, h7⟩ := of_not_modeRegs hr; exact keep₅ r h1 h4 h3 h6 h7
  obtain saved₅ : ∀ i < 7, s₅.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi7 => by
    rw [← hi.saved i hi7]
    refine (f₅.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact slotOut i hi7 (.inr (.inr (.inl rfl)))
      · exact slotOut i hi7 (.inr (.inr (.inr rfl)))) (by decide)).trans ?_
    refine (f₂.readW (Region.contains_self _ _) (hp.stk.coreFrame_disj (slotOut i hi7 (.inr (.inl rfl)))
      ⟨_, hp.scr.wr, VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
        simp only [Core.ctrSlots]; omega_arith)⟩) (by decide)).trans ?_
    exact f₁.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact slotOut i hi7 (.inl rfl)) (by decide)
  obtain fr₅ : Frame ([S, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s₅.mem :=
    hi.frame.trans (((f₁.sub fun r hr => ⟨S, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (f₂.sub (coreFrame_sub ⟨S, List.mem_cons_self, subCore⟩))).trans
      (f₅.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩))
  -- The input block and the data.
  obtain hPout : ∀ u < 8 * c.bw, s₃.mem (P + BitVec.ofNat 64 u) = s.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    obtain hc : (⟨P, 8 * c.bw⟩ : Region).Contains (P + BitVec.ofNat 64 u) 1 :=
      VG.Offset.contains_base P (by omega_arith) (by omega_arith)
    rw [m₃, writeW8_apply, ite_eq_right (fun h => dAP _ (by rw [h]; exact Region.contains_self A 1) hc),
      out₂ _ (fun R hR hR' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl
        · exact dTP _ hR' hc
        · exact dPcore _ hc hR')
      (fun R hR hR' => hp.stk.disj ⟨_, hp.ivw, fun _ h => h⟩ R hR _ hc hR')]
  obtain ivB₅ : ∀ u < 8 * c.bw, s₅.mem (P + BitVec.ofNat 64 u) = (cfb8In enc ciph m₀ D iv (j + 1)).getD u 0 :=
    fun u hu => by
      rw [mem₅, P₄ u hu, cfb8In_succ_getD enc ciph m₀ D hiv hL0 j hu]
      split
      · rename_i h; rw [hPout _ h, hi.ivB _ h]
      · rfl
  obtain data₅' : ∀ q < n, s₅.mem (D + BitVec.ofNat 64 q) =
      if q < j + 1 then cfb8Out enc ciph m₀ D iv q else m₀ (D + BitVec.ofNat 64 q) := fun q hq => by
    obtain hcD : (⟨D, n⟩ : Region).Contains (D + BitVec.ofNat 64 q) 1 := VG.Offset.contains_base D (by omega_arith) (by omega_arith)
    obtain hnP : ¬ (⟨P, 8 * c.bw⟩ : Region).Contains (D + BitVec.ofNat 64 q) 1 := fun h => hp.sepPD _ h hcD
    rw [mem₅, f₄ _ (fun R hR => by simp only [List.mem_singleton] at hR; subst hR; exact hnP), m₃, writeW8_apply]
    by_cases hqj : q = j
    · rw [ite_eq_left (by rw [hqj]), ite_eq_left (by omega_arith), A₂, T₂, hqj]; rfl
    · have hne : D + BitVec.ofNat 64 q ≠ A := fun h => hqj (by
        have := (sub_eq_iff (x := D + BitVec.ofNat 64 q) (P := D) (i := j) (by omega_arith)).mp h
        rwa [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this)
      rw [ite_eq_right hne, out₂ _ (fun R hR hR' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl
        · exact (hp.sepD.sub_right subT) _ hcD hR'
        · exact dDcore _ hcD hR')
        (fun R hR hR' => hp.stk.disj ⟨_, hp.dat, fun _ h => h⟩ R hR _ hcD hR'), hi.data q hq]
      by_cases h3 : q < j
      · rw [ite_eq_left h3, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right h3, ite_eq_right (by omega_arith)]
  by_cases hdone : j + 1 = n
  · exact .inl ⟨by rw [hz₅, decide_eq_true hdone], base₅, rsp₅, saved₅, by rw [← hdone]; exact ivB₅,
      fun q hq => by rw [data₅' q hq, ite_eq_left (by omega_arith)], fr₅, rd₅', wr₅', xmm₅⟩
  · exact .inr ⟨by rw [hz₅, decide_eq_false hdone], base₅, rsp₅, ready₅, saved₅, data₅, left₅, by omega_arith, ivB₅,
      data₅', fr₅, rd₅', wr₅', xmm₅⟩

/-- The data loop. -/
theorem cfb8Loop_wp (cs : BlockSpec c) (enc : Bool) {s₀ : State} {m₀ : Mem} {B D P : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : C8Pre c s₀ B D P n) (hsc : KeepsIv c.crypt)
    {s : State} (hi : C8Inv cs enc s₀ m₀ B D P n k iv 0 s) :
    WP isa (.loop (c.cfb8Block enc) .ne) s (C8Done cs enc s₀ m₀ B D P n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ C8Inv cs enc s₀ m₀ B D P n k iv j s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (cfb8Block_wp cs enc hiv hp hsc hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], n - (j + 1), by have := d.lt; have := hj.lt; omega_arith, j + 1, rfl, d⟩

end VG.Proof.Modes.X86_64

end

end


/-!
# CFB8 on x86-64, for any core: the whole function

`cfb8_wp`: `c.cfb8 enc r`, for a core `c` with `BlockSpec c` whose cipher
is the forward cipher `CIPH_K`, and its arguments in the registers `r`,
replaces the `n` bytes at `D` with CFB8's output (`cfb8Out`) under the key
`k` that its key arguments give, from the input block at `P`, and that
block with the input block after the last byte (`cfb8In`); it keeps the
callee-saved registers, and writes nothing but the scratch buffer, the data
and the input block. `cfb8Enc_of` and `cfb8Dec_of` (`Proof/Modes/Cfb8.lean`)
state these as the specification's.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem cfb8_wp (cs : BlockSpec c) (enc : Bool) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n)
    {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P)
    (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr) (hwD : (⟨D, n⟩ : Region) ∈ s₀.wr)
    (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩) (sDS : Region.Disjoint ⟨D, n⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, n⟩) (fitD : D.toNat + n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩] k) (hsc : KeepsIv c.prepare ∧ KeepsIv c.crypt)
    (hstk : StkOk c s₀ := by exact Or.inl rfl) :
    WP isa (c.cfb8 enc r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      bytesAt s'.mem D n = (List.range n).map (cfb8Out enc (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw))) ∧
      bytesAt s'.mem P (8 * c.bw) = cfb8In enc (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw)) n ∧
      Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  obtain hL0 : 0 < 8 * c.bw := by omega_using [hbw0]
  obtain hn64 : n < 2 ^ 64 := by rw [← hn]; exact BitVec.isLt _
  obtain hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_using [hsm]
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, dbp, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, lbp, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  let S : Region := ⟨B, 8 * c.ctrSlots⟩
  obtain subMode : Region.Sub (modeRegion c B) S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_using [hroom])
  obtain subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by simp only [Core.ctrSlots]; omega_using [hroom])
  obtain inS : ∀ {d m : Nat}, d + m ≤ 8 * c.ctrSlots → InRegions s₀.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hs.wr, VG.Offset.contains_base B h (by omega_using [hN, h])⟩
  obtain slotIn : ∀ i < 7, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_using [hroom, hi])
  obtain slotCore : ∀ i < 7, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ (coreRegion c B) := fun i hi =>
    VG.Offset.disjoint_base B (by omega_using []) (by omega_using [hsm, hroom, hi])
  -- The entry.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨sS, eS, xS, gS, mS, rdS, wrS⟩ := movqX_ok sE Core.ivX r.ctr
  obtain ⟨sA, eA, drA, lrA, gA, mA, rdA, wrA⟩ := ctrArgs_ok sS r hdn hdl
  unfold Core.cfb8
  refine WP.seq (WP.of_runBlock ⟨sA, by
    rw [Core.fbEntry, runBlock_app, runBlock_app, eE, Option.bind_some, eS, Option.bind_some, eA], ?_⟩)
  obtain gA' : ∀ x, x ≠ sb → x ≠ c.dataReg → x ≠ c.leftReg → sA.gpr x = s₀.gpr x := fun x h1 h2 h3 => by
    rw [gA x h2 h3, gS, gE x h1]
  obtain bA : sA.gpr sb = B := by rw [gA _ (Ne.symm dsb) (Ne.symm lsb), gS, bE]
  obtain rdA' : sA.rd = s₀.rd := by rw [rdA, rdS, rdE]
  obtain wrA' : sA.wr = s₀.wr := by rw [wrA, wrS, wrE]
  obtain fA : Frame [S] s₀.mem sA.mem := by
    rw [mA, mS]
    exact fE.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subMode⟩
  let sv : Nat → BitVec 64 := fun i => s₀.gpr (Core.savedRegs.getD i .rbx)
  obtain svA : ∀ i < 6, sA.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [mA, mS, svE i hi]
  obtain xA : sA.xmm Core.ivX = (0 : BitVec 64) ++ P := by
    rw [runBlock_vec rfl eA, xS, gE _ hr.ctr.1, hP]
  obtain kr := keyRegs_ne cs.keyRegs_ok
  obtain hkA : cs.KeyArgs sA [S] k :=
    cs.keyArgs_congr hk (fun x hx => gA' x (kr x hx).1 (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rdA' wrA'
      (by rw [runBlock_syms eA, runBlock_syms eS, runBlock_syms eE]) fA
  -- The key.
  refine WP.seq (WP.mono (WP.keepIv hsc.1 (by rw [xA]; exact hi_zero_append _) (cs.prepare_wp bA ⟨by rw [wrA']; exact hs.wr, hs.fit⟩ List.mem_cons_self hkA))
    fun s₄ ⟨⟨ready₄, b₄, rsp₄, dr₄, lr₄, f₄, rd₄, wr₄⟩, x₄⟩ => ?_)
  rw [show sA.gpr .rsp = s₀.gpr .rsp from gA' _ (by decide) (Ne.symm dsp) (Ne.symm lsp)] at f₄
  obtain rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rdA']
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wrA']
  -- Any bytes?
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := testSelf_ok s₄ c.leftReg
  refine WP.seq (WP.of_runBlock ⟨s₅, e₅, ?_⟩)
  have mem₅ : s₅.mem = s₄.mem := m₅
  obtain b₅ : s₅.gpr sb = B := by rw [g₅, b₄]
  obtain rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by rw [g₅, rsp₄, gA' _ (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  obtain rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄']
  obtain wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄']
  obtain left₅ : s₅.gpr c.leftReg = s₀.gpr r.n := by rw [g₅, lr₄, lrA, gS, gE _ hr.n.1]
  obtain hz₅ : s₅.zf = some (decide (n = 0)) := by
    rw [z₅, ← g₅, left₅]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  obtain sv₅ : ∀ i < 6, s₅.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [mem₅, ← svA i hi]
    exact f₄.readW (Region.contains_self _ _)
      (hstk.coreFrame_disj (slotCore i (by omega_using [hi])) ⟨_, hs.wr, slotIn i (by omega_using [hi])⟩) (by decide)
  obtain x₅ : s₅.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [runBlock_vec rfl e₅, x₄, xA]
  obtain dDcore : ∀ x ∈ coreFrame c B (s₀.gpr .rsp), Region.Disjoint ⟨D, n⟩ x :=
    hstk.coreFrame_disj (sDS.sub_right subCore) ⟨_, hwD, fun _ h => h⟩
  obtain dPcore : ∀ x ∈ coreFrame c B (s₀.gpr .rsp), Region.Disjoint ⟨P, 8 * c.bw⟩ x :=
    hstk.coreFrame_disj (sPS.sub_right subCore) ⟨_, hwP, fun _ h => h⟩
  obtain m₅P : ∀ u < 8 * c.bw, s₅.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [mem₅, f₄.bytes (R := ⟨P, 8 * c.bw⟩) dPcore (show 8 * c.bw ≤ 2 ^ 64 by omega_using [hbw2]) hu]
    exact fA.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sPS)
      (show 8 * c.bw ≤ 2 ^ 64 by omega_using [hbw2]) hu
  obtain m₅D : ∀ q < n, s₅.mem (D + BitVec.ofNat 64 q) = s₀.mem (D + BitVec.ofNat 64 q) := fun q hq => by
    rw [mem₅, f₄.bytes (R := ⟨D, n⟩) dDcore (show n ≤ 2 ^ 64 by omega_using [hn]) hq]
    exact fA.bytes (R := ⟨D, n⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sDS)
      (show n ≤ 2 ^ 64 by omega_using [hn]) hq
  let iv := bytesAt s₀.mem P (8 * c.bw)
  obtain hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  obtain hp : C8Pre c s₅ B D P n := ⟨⟨by rw [wr₅']; exact hs.wr, hs.fit⟩, by rw [wr₅']; exact hwD,
    by rw [wr₅']; exact hwP, sDS, sPS, sPD, fitD, hn64, x₅, hstk.congr rsp₅ wr₅'⟩
  obtain f₄' : Frame (S :: stkList c (s₀.gpr .rsp)) sA.mem s₄.mem := f₄.sub fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨S, List.mem_cons_self, subCore⟩
    · exact ⟨x, List.mem_cons_of_mem _ hx, fun _ h => h⟩
  obtain fr₅ : Frame (S :: stkList c (s₀.gpr .rsp)) s₀.mem s₅.mem := by
    rw [mem₅]
    exact (fA.mono fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self).trans f₄'
  -- The bytes.
  refine WP.seq (WP.mono (M := isa) (Q := C8Done cs enc s₅ s₀.mem B D P n k iv)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₅]) (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₅, rfl, fun _ _ => rfl, fun u hu => by rw [hn0, m₅P u hu]; simp [cfb8In, iv, bytesAt, hu],
      fun q hq => by omega, Frame.refl _ _, rfl, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cfb8Loop_wp cs enc hiv hp hsc.2 ⟨b₅, rfl, cs.ready_frame ready₄ (by rw [mem₅]; exact Frame.refl [] _)
        (fun _ h => by simp at h) ⟨fun _ h => by simp at h, rd₅, wr₅, runBlock_syms e₅⟩ (fun r _ => by rw [g₅]), fun _ _ => rfl, ?_, ?_, by omega_using [hn0],
      fun u hu => by rw [m₅P u hu]; simp [cfb8In, iv, bytesAt, hu], fun q hq => ?_, Frame.refl _ _, rfl, rfl, rfl⟩
    · rw [g₅, dr₄, drA, gS, gE _ hr.data.1, hD]; simp
    · rw [left₅, Nat.sub_zero, ← hn]; simp
    · rw [ite_eq_right (Nat.not_lt_zero _)]; exact m₅D q hq
  -- The exit.
  obtain hsv7 : ∀ i < 6, s₆.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [d₆.saved i (by omega_using [hi]), sv₅ i hi]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₅']
  obtain wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₅']
  obtain hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  obtain hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₈, e₈, v₈, o₈, m₈, rd₈, wr₈⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₆
    d₆.base hsv hinj (fun i hi' => by
      rw [rd₆, wr₆]
      exact inRd (inS (by simp only [Core.ctrSlots]; omega_using [hroom, hi'])))
  refine WP.of_runBlock ⟨s₈, e₈, fun x hx => ?_, ?_, ?_, ?_, by rw [rd₈, rd₆], by rw [wr₈, wr₆]⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain hsaved : ∀ i < 6, s₈.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₈ i hi', hsv7 i (by omega_using [hi'])]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₈ _ (fun i hi' => by revert i; decide), d₆.rsp, rsp₅]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · rw [m₈]
    apply List.ext_getElem (by simp [bytesAt])
    intro q h1 _
    obtain hq : q < n := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact d₆.data q hq
  · rw [m₈]
    apply List.ext_getElem (by
      rw [cfb8In_length (iv := bytesAt s₀.mem P (8 * c.bw)) enc _ _ _ (by simp [bytesAt]) hL0]; simp [bytesAt])
    intro u h1 _
    obtain hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [d₆.ivB u hu, List.getElem_eq_getD 0]
    rfl
  · rw [m₈]
    exact (fr₅.mono fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_append_right _ hx).trans (by rw [← rsp₅]; exact d₆.frame)

end VG.Proof.Modes.X86_64

end

end

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on x86-64 meet their contracts

`ofb_wp`, …: the modes' OFB, CFB and CFB8 (`Proof.Modes.X86_64.fb_wp`,
`cfb8_wp`) over Triple DES encryption's core (`dirCoreSpec .encrypt`), with
the specification's results (`Proof.Modes.ofb_of`, …). `ofb_verified`, …:
each is correct and constant time, by the taint analysis: the pointers, the
length and the stack pointer are public, and so is everything the code
computes from them; the IV is secret. `ofb_framed`, … run them with their
working space on the stack, zeroed on return: 976 bytes, the 121 words of
the scratch buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- The precondition of the feedback modes on x86-64, with the data `len`
bytes long and the working space at `r8`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .rdi, 384⟩
  let iv : Region := ⟨s.gpr .rsi, 8⟩
  let data : Region := ⟨s.gpr .rdx, len s⟩
  let scratch : Region := ⟨s.gpr .r8, 8 * 121⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 121 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 8 * (s.gpr .rcx).toNat

/-- `len` bytes. -/
abbrev byteLen (s : State) : Nat := (s.gpr .rcx).toNat

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi))
abbrev ivOf (s : State) : List Byte := Spec.TripleDes.bytesAt s.mem (s.gpr .rsi) 8
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.TripleDes.cbcBlocksAt m (s.gpr .rdx) (s.gpr .rcx).toNat

def ofbX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .rcx).toNat
  pub := fbPub

def cfbEncX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfb8EncX86_64 : Contract isa where
  pre := fbPre byteLen
  post s s' := Spec.TripleDes.bytesAt s'.mem (s.gpr .rdx) (byteLen s) =
      Spec.Cfb8.encrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .rdx) (byteLen s)) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Cfb8.next (ivOf s)
      (Spec.Cfb8.encrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .rdx) (byteLen s)))
  pub := fbPub

def cfb8DecX86_64 : Contract isa where
  pre := fbPre byteLen
  post s s' := Spec.TripleDes.bytesAt s'.mem (s.gpr .rdx) (byteLen s) =
      Spec.Cfb8.decrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .rdx) (byteLen s)) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cfb8.next (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .rdx) (byteLen s))
  pub := fbPub

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the
IV as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa ((dirCore .encrypt).fb mo fbRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat =
        (List.range (s₀.gpr .rcx).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀)) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .rsi) 8 = Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 121⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fb_wp (dirCoreSpec .encrypt) mo (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV

/-- What the modes' CFB8 gives: the data and the input block as `cfb8Out`
and `cfb8In`, keeping the callee-saved registers. -/
theorem cfb8_wp' (enc : Bool) {s₀ : State} (hp : fbPre byteLen s₀) :
    WP isa ((dirCore .encrypt).cfb8 enc fbRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .rdx) (byteLen s₀) =
        (List.range (byteLen s₀)).map (Modes.cfb8Out enc (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀)) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .rsi) 8 =
        Modes.cfb8In enc (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (byteLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 121⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cfb8_wp (dirCoreSpec .encrypt) enc (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV

theorem ofb_wp {s₀ : State} (hp : ofbX86_64.pre s₀) :
    WP isa ofbI s₀ fun s' => gprPreserved s₀ s' ∧ ofbX86_64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX86_64.pre s₀) :
    WP isa cfbEncryptI s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _))
      rw [hv, h2, cbcBlocksAt_eq]

theorem ivOf_ne (s : State) : ivOf s ≠ [] := by simp [ivOf, Spec.TripleDes.bytesAt]

theorem cfb8Encrypt_wp {s₀ : State} (hp : cfb8EncX86_64.pre s₀) :
    WP isa cfb8EncryptI s₀ fun s' => gprPreserved s₀ s' ∧ cfb8EncX86_64.post s₀ s' :=
  WP.mono (cfb8_wp' true hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfb8Enc_of (ciphOf s₀) s₀.mem (byteLen s₀) (s₀.gpr .rdx) (ivOf s₀) (ivOf_ne s₀)
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfb8Decrypt_wp {s₀ : State} (hp : cfb8DecX86_64.pre s₀) :
    WP isa cfb8DecryptI s₀ fun s' => gprPreserved s₀ s' ∧ cfb8DecX86_64.post s₀ s' :=
  WP.mono (cfb8_wp' false hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfb8Dec_of (ciphOf s₀) s₀.mem (byteLen s₀) (s₀.gpr .rdx) (ivOf s₀) (ivOf_ne s₀)
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

/-! ## Constant time -/

def fbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [8, 0, 8 * 121], bases := [(.r8, 2, 0)] }

theorem fbTaint_wf {len : State → Nat} (s : State) (hs : fbPre len s) : Taint.Wf fbTaint s := by
  obtain ⟨_, hwr, _, _, _, dVD, dVS, dDS, _, _, _, _, fitV, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 8 ≤ 8; omega_using []) (List.Forall₂.cons (by change 0 ≤ len s; omega_using [])
        (List.Forall₂.cons (by change 8 * 121 ≤ 8 * 121; omega_using []) List.Forall₂.nil))
    · refine List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons (fun r hr => ?_)
        (List.Pairwise.cons (by simp) List.Pairwise.nil))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dVD
        · exact dVS
      · obtain rfl := List.mem_singleton.mp hr; exact dDS
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change 8 ≤ 2 ^ 64; omega_using []
      · change len s ≤ 2 ^ 64; omega_using [fitD]
      · change 8 * 121 ≤ 2 ^ 64; omega_using []
  · intro p hp
    simp only [fbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .r8 = s.gpr .r8 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem fbTaint_agree {len : State → Nat} (hlen : ∀ s t, s.gpr .rcx = t.gpr .rcx → len s = len t) (s t : State)
    (hs : fbPre len s) (ht : fbPre len t) (hp : fbPub s t) : X86_64.Taint.Agree fbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine ⟨?_, ?_, fbTaint_wf s hs, fbTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5, p6]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, p2, p3, p5, hlen s t p4]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [fbTaint, RegSet.not_mem_empty] at hr

theorem blkLen_congr : ∀ s t : State, s.gpr .rcx = t.gpr .rcx → blkLen s = blkLen t := fun _ _ h => by
  simp only [blkLen, h]

theorem byteLen_congr : ∀ s t : State, s.gpr .rcx = t.gpr .rcx → byteLen s = byteLen t := fun _ _ h => by
  simp only [byteLen, h]

/-- A state satisfying the precondition (one block, or one byte). -/
def fbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 8 * 121⟩]

def cfb8Sat : State := { fbSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 121⟩] }

theorem ofb_correct (s : State) (hs : ofbX86_64.pre s) :
    ∃ t s', Exec isa ofbI s t s' ∧ abiPreserved s s' ∧ ofbX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := ofb_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := ofbI) (by lit_decide) he hg, hpost⟩

theorem ofb_ct : ConstantTime isa ofbX86_64.pre ofbX86_64.pub ofb := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint ofb h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree blkLen_congr) h

theorem ofb_implies : ofbX86_64.Implies (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.ofbPost) := by
    sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Proof.TripleDes.ofbPost, ofbX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat

theorem ofb_implies8 : ofbX86_64.Implies (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.ofbPost 8) :=
  ofb_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, X86_64.abi, X86_64.argRegs, fbSat] [fbSat]
      using fbSat)

/-- The data and the IV are apart from the call's return address. -/
theorem ofb_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.ofbPost 8).pre s) (hp : ofbX86_64.post s b) :
    ofbX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := ofb_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := 8 * (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by simp only [blkLen] at fitD; omega_using [fitD])
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega_using [])
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · show Spec.TripleDes.cbcBlocksAt _ _ _ = _
    rw [cbcBlocksAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem ofb_inline : ofb.inline = ofbI := rfl

theorem ofb_verified :
    Verified X86_64.target ofb (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.ofbPost 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [ofb_inline]; exact ofb_correct s hs) ofb_ct
    ofb_implies8 (fun _ h => Sig.clear_of_pre h) ofb_patch

theorem cfbEncrypt_correct (s : State) (hs : cfbEncX86_64.pre s) :
    ∃ t s', Exec isa cfbEncryptI s t s' ∧ abiPreserved s s' ∧ cfbEncX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncryptI) (by lit_decide) he hg, hpost⟩

theorem cfbEncrypt_ct : ConstantTime isa cfbEncX86_64.pre cfbEncX86_64.pub cfbEncrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint cfbEncrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree blkLen_congr) h

theorem cfbEncrypt_implies : cfbEncX86_64.Implies (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbEncPost) := by
    sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Proof.TripleDes.cfbEncPost, cfbEncX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat

theorem cfbEncrypt_implies8 : cfbEncX86_64.Implies (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbEncPost 8) :=
  cfbEncrypt_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, X86_64.abi, X86_64.argRegs, fbSat] [fbSat]
      using fbSat)

/-- The data and the IV are apart from the call's return address. -/
theorem cfbEncrypt_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbEncPost 8).pre s) (hp : cfbEncX86_64.post s b) :
    cfbEncX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cfbEncrypt_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := 8 * (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by simp only [blkLen] at fitD; omega_using [fitD])
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega_using [])
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · show Spec.TripleDes.cbcBlocksAt _ _ _ = _
    rw [cbcBlocksAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem cfbEncrypt_inline : cfbEncrypt.inline = cfbEncryptI := rfl

theorem cfbEncrypt_verified :
    Verified X86_64.target cfbEncrypt (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbEncPost 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [cfbEncrypt_inline]; exact cfbEncrypt_correct s hs) cfbEncrypt_ct
    cfbEncrypt_implies8 (fun _ h => Sig.clear_of_pre h) cfbEncrypt_patch

theorem cfb8Encrypt_correct (s : State) (hs : cfb8EncX86_64.pre s) :
    ∃ t s', Exec isa cfb8EncryptI s t s' ∧ abiPreserved s s' ∧ cfb8EncX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfb8Encrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfb8EncryptI) (by lit_decide) he hg, hpost⟩

theorem cfb8Encrypt_ct : ConstantTime isa cfb8EncX86_64.pre cfb8EncX86_64.pub cfb8Encrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint cfb8Encrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree byteLen_congr) h

theorem cfb8Encrypt_implies : cfb8EncX86_64.Implies (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8EncPost) := by
    sig_implies [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig,
      Proof.TripleDes.cfb8EncPost, cfb8EncX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [cfb8Sat] using cfb8Sat

theorem cfb8Encrypt_implies8 : cfb8EncX86_64.Implies (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8EncPost 8) :=
  cfb8Encrypt_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, X86_64.abi, X86_64.argRegs, cfb8Sat] [cfb8Sat]
      using cfb8Sat)

/-- The data and the IV are apart from the call's return address. -/
theorem cfb8Encrypt_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8EncPost 8).pre s) (hp : cfb8EncX86_64.post s b) :
    cfb8EncX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cfb8Encrypt_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by omega_using [])
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega_using [])
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [bytesAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem cfb8Encrypt_inline : cfb8Encrypt.inline = cfb8EncryptI := rfl

theorem cfb8Encrypt_verified :
    Verified X86_64.target cfb8Encrypt (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8EncPost 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [cfb8Encrypt_inline]; exact cfb8Encrypt_correct s hs) cfb8Encrypt_ct
    cfb8Encrypt_implies8 (fun _ h => Sig.clear_of_pre h) cfb8Encrypt_patch

theorem cfb8Decrypt_correct (s : State) (hs : cfb8DecX86_64.pre s) :
    ∃ t s', Exec isa cfb8DecryptI s t s' ∧ abiPreserved s s' ∧ cfb8DecX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfb8Decrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfb8DecryptI) (by lit_decide) he hg, hpost⟩

theorem cfb8Decrypt_ct : ConstantTime isa cfb8DecX86_64.pre cfb8DecX86_64.pub cfb8Decrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint cfb8Decrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree byteLen_congr) h

theorem cfb8Decrypt_implies : cfb8DecX86_64.Implies (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8DecPost) := by
    sig_implies [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig,
      Proof.TripleDes.cfb8DecPost, cfb8DecX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [cfb8Sat] using cfb8Sat

theorem cfb8Decrypt_implies8 : cfb8DecX86_64.Implies (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8DecPost 8) :=
  cfb8Decrypt_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, X86_64.abi, X86_64.argRegs, cfb8Sat] [cfb8Sat]
      using cfb8Sat)

/-- The data and the IV are apart from the call's return address. -/
theorem cfb8Decrypt_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8DecPost 8).pre s) (hp : cfb8DecX86_64.post s b) :
    cfb8DecX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cfb8Decrypt_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by omega_using [])
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega_using [])
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [bytesAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem cfb8Decrypt_inline : cfb8Decrypt.inline = cfb8DecryptI := rfl

theorem cfb8Decrypt_verified :
    Verified X86_64.target cfb8Decrypt (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8DecPost 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [cfb8Decrypt_inline]; exact cfb8Decrypt_correct s hs) cfb8Decrypt_ct
    cfb8Decrypt_implies8 (fun _ h => Sig.clear_of_pre h) cfb8Decrypt_patch

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 ofb)
      (Spec.TripleDes.ofbContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.ofbPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) ofb_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.ofbPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cfbEncrypt)
      (Spec.TripleDes.cfbEncryptContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cfbEncPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cfbEncrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cfbEncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB8 encryption with its working space on the stack. -/
theorem cfb8Encrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cfb8Encrypt)
      (Spec.TripleDes.cfb8EncryptContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cfb8EncPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cfb8Encrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cfb8EncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB8 decryption with its working space on the stack. -/
theorem cfb8Decrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cfb8Decrypt)
      (Spec.TripleDes.cfb8DecryptContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cfb8DecPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cfb8Decrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cfb8DecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.TripleDes.X86_64
