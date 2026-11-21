module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Impl.Rc2.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Chained
public import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Rc2.CbcScratch
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Chained
meta import VerifiedGarbage.Proof.Rc2.Scratch
meta import VerifiedGarbage.Proof.Rc2.CbcScratch
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Rc2.RISCV64.Stream
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.Impl.Rc2.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Rc2.PiLit
public import VerifiedGarbage.Proof.Rc2.Expansion
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Rc2.Table
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Rc2.Expansion
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Loops
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Impl.Rc2.RISCV64.ExpandKey
meta import VerifiedGarbage.Proof.Rc2.Table
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Rc2.RISCV64.Stream
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Rc2.Stream
meta import VerifiedGarbage.Proof.Rc2.Memory
meta import VerifiedGarbage.Proof.Rc2.CbcMemory
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Rc2.PiLit

/-! ### `Rc2.RISCV64.Stream.Frame`, which only this module used -/

section

/-! ### `Rc2.RISCV64.Stream.Verified`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.Stream.Init`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.KeyVerified`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.Key`, which only this module used -/

section

/-! ### `Rc2.RISCV64.KeySteps`, which only this module used -/

section

/-!
# RC2 on RISC-V: the steps of key expansion

`piLookup_run`: the scan of PITABLE in the working space leaves `pi q` in
`t1`. Each step of the loops (`copy_run`, `fill_run`, `reduce_run`,
`descend_run`) stores one byte of `L`.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

theorem piRegs : ScanRegs .a4 := ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- A byte's lane is its low three bits. -/
theorem byte_lane (q : BitVec 64) : (q &&& BitVec.ofNat 64 7).toNat = q.toNat % 8 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show 7 % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- The scan of PITABLE at `a4`. -/
theorem piLookup_run (s : State) {W : Addr} (hW : s.gpr .a4 = W) (hal : W.toNat % 8 = 0) (hq : (s.gpr .t0).toNat < 256)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (8 * k)) 8) (hP : Proof.Rc2.PiHeld s.mem W) :
    WP isa piLookup s fun t =>
      t.gpr .t1 = (Spec.Rc2.pi ((s.gpr .t0).setWidth 8)).setWidth 64 ∧
      Keep [.a7, .t1, .t2, .t3] s t ∧ t.mem = s.mem := by
  refine WP.mono (scan_run piRegs s hW hal (rows := 32) (by decide) (laneBits := 7) (by decide)
    (bits := 8) (by decide) hq (byte_lane _) hr) fun t ⟨t11, tk, tm⟩ => ⟨?_, tk, tm⟩
  have e : W + s.gpr .t0 = W + BitVec.ofNat 64 (s.gpr .t0).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [t11, entry_byte, e, hP.byte hq]
  refine congrArg (BitVec.setWidth 64) ?_
  simp only [Spec.Rc2.pi, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hq]

theorem lo8_ext (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b :=
  BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq b)

theorem copy_run (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .a0 + s.gpr .a5) 1)
    (hw : InRegions s.wr (s.gpr .a3 + s.gpr .a5) 1) :
    WP isa (.block copyKey) s fun t =>
      t.gpr .a5 = s.gpr .a5 + 1#64 ∧ t.gpr .a7 = s.gpr .a5 + 1#64 - s.gpr .a1 ∧
      t.mem = s.mem.writeW (s.gpr .a3 + s.gpr .a5) (s.mem (s.gpr .a0 + s.gpr .a5)) ∧
      Keep [.a7, .a5, .a6, .t2] s t := by
  refine WP.mono (WP.keep [.a7, .a5, .a6, .t2] (c := .block copyKey) (Q := fun t =>
      t.gpr .a5 = s.gpr .a5 + 1#64 ∧ t.gpr .a7 = s.gpr .a5 + 1#64 - s.gpr .a1 ∧
      t.mem = s.mem.writeW (s.gpr .a3 + s.gpr .a5) (s.mem (s.gpr .a0 + s.gpr .a5))) ?_
    (by rfl) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  unfold copyKey
  rrun [hr, hw, lo8_ext]

theorem ext_lt (b : BitVec 8) : (b.setWidth 64).toNat < 256 := by
  rw [BitVec.toNat_setWidth]; have := b.isLt; omega_using []

theorem ext_and (a : BitVec 8) (y : BitVec 64) : a.setWidth 64 &&& y = (a &&& y.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [h, BitVec.getLsbD_of_ge a i (by omega_using [h])]

theorem ext_xor (a b : BitVec 8) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [BitVec.getLsbD_of_ge a i (by omega_using [h]), BitVec.getLsbD_of_ge b i (by omega_using [h])]

theorem ext_add (a b : BitVec 8) : ((a.setWidth 64 + b.setWidth 64) <<< 56) >>> 56 = (a + b).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 by omega_using []), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega_using []),
    Nat.mod_eq_of_lt (show a.toNat + b.toNat < 2 ^ 64 by omega_using [])]
  omega_using []

/-- The registers the steps of key expansion write. -/
abbrev keyTemps : List Reg := [.a7, .a5, .a6, .t0, .t1, .t2, .t3]

/-- The scan's environment: PITABLE at `W` in the working space at `a4`. -/
structure PiEnv (W : Addr) (s : State) : Prop where
  a4 : s.gpr .a4 = W
  al : W.toNat % 8 = 0
  rd : ∀ k < 32, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (8 * k)) 8
  held : Proof.Rc2.PiHeld s.mem W

theorem PiEnv.keep {W : Addr} {s t : State} (E : PiEnv W s) {rs : List Reg} (k : Keep rs s t)
    (h7 : Reg.a4 ∉ rs) (hm : t.mem = s.mem) : PiEnv W t :=
  ⟨by rw [k.gpr h7]; exact E.a4, E.al, fun j hj => by rw [k.2.1, k.2.2]; exact E.rd j hj, by rw [hm]; exact E.held⟩

/-- A byte through the scan and into `L[i]`: the scan and `storeKey`. -/
theorem piStore_run (s : State) {W : Addr} (E : PiEnv W s) (hq : (s.gpr .t0).toNat < 256)
    (hw : InRegions s.wr (s.gpr .a3 + s.gpr .a5) 1) :
    WP isa (.seq piLookup (.block storeKey)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .a3 + s.gpr .a5) (Spec.Rc2.pi ((s.gpr .t0).setWidth 8)) ∧
      Keep [.a7, .t1, .t2, .t3, .a6] s t := by
  apply WP.seq
  refine WP.mono (piLookup_run s E.a4 E.al hq E.rd E.held) fun t₁ ⟨a₁, k₁, m₁⟩ => ?_
  have h6 : t₁.gpr .a3 = s.gpr .a3 := k₁.gpr (by decide)
  have h8 : t₁.gpr .a5 = s.gpr .a5 := k₁.gpr (by decide)
  refine WP.mono (WP.keep [.a6] (c := .block storeKey) (Q := fun t =>
      t.mem = t₁.mem.writeW (t₁.gpr .a3 + t₁.gpr .a5) ((t₁.gpr .t1).setWidth 8)) ?_
    (by rfl) rfl) fun t ⟨a, k⟩ =>
      ⟨by rw [a, a₁, m₁, h6, h8, lo8_ext], (k₁.trans k).mono (by simp)⟩
  unfold storeKey
  rrun [show InRegions t₁.wr (t₁.gpr .a3 + t₁.gpr .a5) 1 by rw [k₁.2.2, h6, h8]; exact hw]

theorem fill_run (s : State) {W : Addr} (E : PiEnv W s)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .a3 + s.gpr .a5 - 1#64) 1)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .a3 + (s.gpr .a5 - s.gpr .a1)) 1)
    (hw : InRegions s.wr (s.gpr .a3 + s.gpr .a5) 1) :
    WP isa fillKey s fun t =>
      t.gpr .a5 = s.gpr .a5 + 1#64 ∧ t.gpr .a7 = s.gpr .a5 + 1#64 - 128#64 ∧
      t.mem = s.mem.writeW (s.gpr .a3 + s.gpr .a5)
        (Spec.Rc2.pi (s.mem (s.gpr .a3 + s.gpr .a5 - 1#64) + s.mem (s.gpr .a3 + (s.gpr .a5 - s.gpr .a1)))) ∧
      Keep keyTemps s t := by
  unfold fillKey
  apply WP.seq
  refine WP.mono (WP.keep [.a6, .t0, .t1] (c := .block fillInput) (Q := fun t =>
      t.gpr .t0 = (s.mem (s.gpr .a3 + s.gpr .a5 - 1#64) + s.mem (s.gpr .a3 + (s.gpr .a5 - s.gpr .a1))).setWidth 64 ∧
      t.mem = s.mem) (by unfold fillInput mask; rrun [hlo, hhi, ext_add])
    (by rfl) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .a3 = s.gpr .a3 := k₁.gpr (by decide)
  have h8 : t₁.gpr .a5 = s.gpr .a5 := k₁.gpr (by decide)
  apply WP.seq
  refine WP.mono (piLookup_run t₁ (E.keep k₁ (by decide) m₁).a4 E.al (by rw [a₁]; exact ext_lt _)
    (E.keep k₁ (by decide) m₁).rd (E.keep k₁ (by decide) m₁).held) fun t₂ ⟨a₂, k₂, m₂⟩ => ?_
  have h6' : t₂.gpr .a3 = s.gpr .a3 := by rw [k₂.gpr (by decide), h6]
  have h8' : t₂.gpr .a5 = s.gpr .a5 := by rw [k₂.gpr (by decide), h8]
  refine WP.mono (WP.keep [.a7, .a5, .a6] (c := .block fillFinish) (Q := fun t =>
      t.gpr .a5 = t₂.gpr .a5 + 1#64 ∧ t.gpr .a7 = t₂.gpr .a5 + 1#64 - 128#64 ∧
      t.mem = t₂.mem.writeW (t₂.gpr .a3 + t₂.gpr .a5) ((t₂.gpr .t1).setWidth 8)) ?_
    (by rfl) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ⟨by rw [a, h8'], by rw [b, h8'], by rw [c, a₂, m₂, m₁, h6', h8', a₁, lo8_ext, lo8_ext],
      ((k₁.trans k₂).trans k).mono (by simp)⟩
  unfold fillFinish storeKey
  rrun [show InRegions t₂.wr (t₂.gpr .a3 + t₂.gpr .a5) 1 by rw [k₂.2.2, k₁.2.2, h6', h8']; exact hw]

theorem reduce_run (s : State) {W : Addr} (E : PiEnv W s) (hr : InRegions (s.rd ++ s.wr) (s.gpr .a3 + s.gpr .a5) 1)
    (hw : InRegions s.wr (s.gpr .a3 + s.gpr .a5) 1) :
    WP isa reduceKey s fun t =>
      t.mem = s.mem.writeW (s.gpr .a3 + s.gpr .a5)
        (Spec.Rc2.pi (s.mem (s.gpr .a3 + s.gpr .a5) &&& (s.gpr .t2).setWidth 8)) ∧
      Keep [.a7, .a6, .t0, .t1, .t2, .t3] s t := by
  unfold reduceKey
  apply WP.seq
  refine WP.mono (WP.keep [.a6, .t0] (c := .block reduceInput) (Q := fun t =>
      t.gpr .t0 = (s.mem (s.gpr .a3 + s.gpr .a5) &&& (s.gpr .t2).setWidth 8).setWidth 64 ∧
      t.mem = s.mem) (by unfold reduceInput; rrun [hr, ext_and])
    (by rfl) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .a3 = s.gpr .a3 := k₁.gpr (by decide)
  have h8 : t₁.gpr .a5 = s.gpr .a5 := k₁.gpr (by decide)
  refine WP.mono (piStore_run t₁ (E.keep k₁ (by decide) m₁) (by rw [a₁]; exact ext_lt _)
    (by rw [k₁.2.2, h6, h8]; exact hw)) fun t ⟨a, k⟩ =>
      ⟨by rw [a, m₁, h6, h8, a₁, lo8_ext], (k₁.trans k).mono (by simp)⟩

theorem descend_run (s : State) {W : Addr} (E : PiEnv W s)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .a3 + (s.gpr .a5 - 1#64) + 1#64) 1)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .a3 + (s.gpr .a5 - 1#64 + s.gpr .t4)) 1)
    (hw : InRegions s.wr (s.gpr .a3 + (s.gpr .a5 - 1#64)) 1) :
    WP isa descendKey s fun t =>
      t.gpr .a5 = s.gpr .a5 - 1#64 ∧
      t.mem = s.mem.writeW (s.gpr .a3 + (s.gpr .a5 - 1#64))
        (Spec.Rc2.pi (s.mem (s.gpr .a3 + (s.gpr .a5 - 1#64) + 1#64) ^^^
          s.mem (s.gpr .a3 + (s.gpr .a5 - 1#64 + s.gpr .t4)))) ∧
      Keep keyTemps s t := by
  unfold descendKey
  apply WP.seq
  refine WP.mono (WP.keep [.a5, .a6, .t0, .t1] (c := .block descendInput) (Q := fun t =>
      t.gpr .a5 = s.gpr .a5 - 1#64 ∧
      t.gpr .t0 = (s.mem (s.gpr .a3 + (s.gpr .a5 - 1#64) + 1#64) ^^^
        s.mem (s.gpr .a3 + (s.gpr .a5 - 1#64 + s.gpr .t4))).setWidth 64 ∧
      t.mem = s.mem) (by unfold descendInput; rrun [hlo, hhi, ext_xor])
    (by rfl) rfl) fun t₁ ⟨⟨i₁, a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .a3 = s.gpr .a3 := k₁.gpr (by decide)
  refine WP.mono (piStore_run t₁ (E.keep k₁ (by decide) m₁) (by rw [a₁]; exact ext_lt _)
    (by rw [k₁.2.2, h6, i₁]; exact hw)) fun t ⟨a, k⟩ =>
      ⟨by rw [k.gpr (by decide), i₁], by rw [a, m₁, h6, i₁, a₁, lo8_ext], (k₁.trans k).mono (by simp)⟩

end VG.Proof.Rc2.RISCV64

end

end

/-! ### `Rc2.RISCV64.KeyLoop`, which only this module used -/

section

/-!
# RC2 on RISC-V: the loops of key expansion

Each loop keeps `KEnv` (the arguments, PITABLE in the working space and the
key) and builds `L` in the schedule (`Proof.Rc2.BytesPrefix`): `copy_loop`, `fill_loop`, `descend_loop`.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- What the loops keep. -/
structure KEnv (K S W : Addr) (len bits : Nat) (key : List Byte) (s : State) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 len
  a2 : s.gpr .a2 = BitVec.ofNat 64 bits
  a3 : s.gpr .a3 = S
  pi : PiEnv W s
  rd : s.rd = [⟨K, len⟩]
  wr : s.wr = [⟨S, 128⟩, ⟨W, 512⟩]
  key : ∀ c < len, s.mem (K + BitVec.ofNat 64 c) = key.getD c 0

/-- The constant facts about the regions. -/
structure KRegions (K S W : Addr) (len : Nat) : Prop where
  hlen : 1 ≤ len ∧ len ≤ 128
  kS : (⟨K, len⟩ : Region).Disjoint ⟨S, 128⟩
  SW : (⟨S, 128⟩ : Region).Disjoint ⟨W, 512⟩

theorem KEnv.keep {K S W : Addr} {len bits : Nat} {key : List Byte} {s t : State}
    (E : KEnv K S W len bits key s) {rs : List Reg} (k : Keep rs s t)
    (h : Reg.a0 ∉ rs ∧ Reg.a1 ∉ rs ∧ Reg.a2 ∉ rs ∧ Reg.a3 ∉ rs ∧ Reg.a4 ∉ rs) (hm : t.mem = s.mem) :
    KEnv K S W len bits key t :=
  ⟨by rw [k.gpr h.1]; exact E.a0, by rw [k.gpr h.2.1]; exact E.a1, by rw [k.gpr h.2.2.1]; exact E.a2,
    by rw [k.gpr h.2.2.2.1]; exact E.a3, E.pi.keep k h.2.2.2.2 hm, by rw [k.2.1]; exact E.rd,
    by rw [k.2.2]; exact E.wr, by rw [hm]; exact E.key⟩

/-- After a step that writes byte `i` of `L`. -/
theorem KEnv.write {K S W : Addr} {len bits : Nat} {key : List Byte} {s t : State}
    (E : KEnv K S W len bits key s) (R : KRegions K S W len) (k : Keep keyTemps s t) {i : Nat} (hi : i < 128)
    {b : Byte} (hm : t.mem = s.mem.writeW (S + BitVec.ofNat 64 i) b) : KEnv K S W len bits key t := by
  have F : Frame [⟨S, 128⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  refine ⟨by rw [k.gpr (by decide)]; exact E.a0, by rw [k.gpr (by decide)]; exact E.a1,
    by rw [k.gpr (by decide)]; exact E.a2, by rw [k.gpr (by decide)]; exact E.a3,
    ⟨by rw [k.gpr (by decide)]; exact E.pi.a4, E.pi.al, fun j hj => by rw [k.2.1, k.2.2]; exact E.pi.rd j hj, fun j hj => ?_⟩,
    by rw [k.2.1]; exact E.rd, by rw [k.2.2]; exact E.wr, fun c hc => ?_⟩
  · rw [F.readW (r := ⟨W, 512⟩) (Offset.contains_base _ (by rw [Proof.Rc2.piQuads_length] at hj; omega_arith)
      (by rw [Proof.Rc2.piQuads_length] at hj; omega_arith)) (by simpa using R.SW.symm) (by decide)]
    exact E.pi.held j hj
  · rw [F.bytes (R := ⟨K, len⟩) (by simpa using R.kS) (by have := R.hlen; simp; omega_arith) hc]
    exact E.key c hc

theorem copy_loop {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) (s : State) (E : KEnv K S W len bits key s) (h8 : s.gpr .a5 = 0#64) :
    WP isa (.loop (.block copyKey) (.nonzero .a7)) s fun t =>
      KEnv K S W len bits key t ∧ t.gpr .a5 = BitVec.ofNat 64 len ∧
        Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key 0) len := by
  have hl := R.hlen
  refine countLoop _ _ (fun i t => KEnv K S W len bits key t ∧ t.gpr .a5 = BitVec.ofNat 64 i ∧
      Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key 0) i) len (fun i hi t ⟨E, h8, P⟩ => ?_) 0 (by omega_arith) s
    ⟨E, h8, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.mono (copy_run t (by rw [E.rd, E.wr, E.a0, h8]; exact ⟨⟨K, len⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (by rw [E.wr, E.a3, h8]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
    fun t' ⟨a, b, m, k⟩ => ?_
  rw [E.a3, E.a0, h8, E.key i hi] at m
  refine ⟨⟨E.write R (k.mono (by simp)) (by omega_arith) m, by rw [a, h8, succ_ofNat], ?_⟩, ?_⟩
  · rw [m, ← Proof.Rc2.initial_set key i]
    exact P.extend (by omega_arith) _
  · rw [b, h8, E.a1, succ_ofNat, sub_bne (by omega_arith) (by omega_arith)]

theorem fill_loop {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) (hk : key.length = len) (hl : len < 128) (s : State) (E : KEnv K S W len bits key s)
    (h8 : s.gpr .a5 = BitVec.ofNat 64 len) (P : Proof.Rc2.BytesPrefix s.mem S (Proof.Rc2.fill key 0) len) :
    WP isa (.loop fillKey (.nonzero .a7)) s fun t =>
      KEnv K S W len bits key t ∧ t.gpr .a5 = BitVec.ofNat 64 128 ∧
        Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (128 - len)) 128 := by
  have hl1 := R.hlen
  refine countLoop _ _ (fun i t => KEnv K S W len bits key t ∧ t.gpr .a5 = BitVec.ofNat 64 i ∧
      Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (i - len)) i ∧ len ≤ i) 128
    (fun i hi t ⟨E, h8, P, hli⟩ => ?_) len hl s ⟨E, h8, by rw [Nat.sub_self]; exact P, Nat.le_refl _⟩
    |> fun h => WP.mono h fun t ⟨a, b, c, _⟩ => ⟨a, b, c⟩
  have lo : t.gpr .a3 + t.gpr .a5 - 1#64 = S + BitVec.ofNat 64 (i - 1) := by
    rw [E.a3, h8, Offset.add_ofNat_sub S (by omega_arith)]
  have hi' : t.gpr .a3 + (t.gpr .a5 - t.gpr .a1) = S + BitVec.ofNat 64 (i - len) := by
    rw [E.a3, h8, E.a1, Offset.ofNat_sub_ofNat hli]
  have inS : ∀ c < 128, InRegions t.wr (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    rw [E.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have inS' : ∀ c < 128, InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    obtain ⟨r, hr, hc⟩ := inS c hc; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (fill_run t E.pi (by rw [lo]; exact inS' _ (by omega_arith)) (by rw [hi']; exact inS' _ (by omega_arith))
    (by rw [E.a3, h8]; exact inS i hi)) fun t' ⟨a, b, m, k⟩ => ?_
  rw [lo, hi', E.a3, h8, P (i - 1) (by omega_arith), P (i - len) (by omega_arith)] at m
  refine ⟨⟨E.write R k hi m, by rw [a, h8, succ_ofNat], ?_, by omega_arith⟩, ?_⟩
  · have e : Proof.Rc2.fill key (i + 1 - len) = (Proof.Rc2.fill key (i - len)).set! i
        (Spec.Rc2.pi ((Proof.Rc2.fill key (i - len)).getD (i - 1) 0 +
          (Proof.Rc2.fill key (i - len)).getD (i - len) 0)) := by
      rw [show i + 1 - len = (i - len) + 1 by omega_arith, Proof.Rc2.fill_succ]
      simp only [Proof.Rc2.fillStep, hk]
      rw [show len + (i - len) = i by omega_arith]
    rw [m, e]
    exact P.extend (by omega_arith) _
  · rw [b, h8, succ_ofNat, sub_bne (by omega_arith) (by omega_arith)]

theorem descend_loop {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) {t8 : Nat} (ht8 : 1 ≤ t8 ∧ t8 < 128) (l : Proof.Rc2.KeyBytes) (s : State)
    (E : KEnv K S W len bits key s) (h8 : s.gpr .a5 = BitVec.ofNat 64 (128 - t8))
    (h14 : s.gpr .t4 = BitVec.ofNat 64 t8) (P : Proof.Rc2.BytesPrefix s.mem S l 128) :
    WP isa (.loop descendKey (.nonzero .a5)) s fun t =>
      KEnv K S W len bits key t ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.descend l t8 (128 - t8)) 128 := by
  refine countLoop _ _ (fun j t => KEnv K S W len bits key t ∧ t.gpr .a5 = BitVec.ofNat 64 (128 - t8 - j) ∧
      t.gpr .t4 = BitVec.ofNat 64 t8 ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.descend l t8 j) 128) (128 - t8)
    (fun j hj t ⟨E, h8, h14, P⟩ => ?_) 0 (by omega_arith) s ⟨E, by rw [h8, Nat.sub_zero], h14, P⟩
    |> fun h => WP.mono h fun t ⟨a, _, _, c⟩ => ⟨a, c⟩
  have hd : t.gpr .a5 - 1#64 = BitVec.ofNat 64 (127 - t8 - j) := by
    rw [h8, Offset.ofNat_sub_ofNat (by omega_arith), show 128 - t8 - j - 1 = 127 - t8 - j by omega_arith]
  have inS : ∀ c < 128, InRegions t.wr (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    rw [E.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have inS' : ∀ c < 128, InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    obtain ⟨r, hr, hc⟩ := inS c hc; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have lo : t.gpr .a3 + (t.gpr .a5 - 1#64) + 1#64 = S + BitVec.ofNat 64 (127 - t8 - j + 1) := by
    rw [E.a3, hd, Offset.add_add]
  have hi' : t.gpr .a3 + (t.gpr .a5 - 1#64 + t.gpr .t4) = S + BitVec.ofNat 64 (127 - t8 - j + t8) := by
    rw [E.a3, hd, h14, BitVec.ofNat_add_ofNat]
  refine WP.mono (descend_run t E.pi (by rw [lo]; exact inS' _ (by omega_arith)) (by rw [hi']; exact inS' _ (by omega_arith))
    (by rw [E.a3, hd]; exact inS _ (by omega_arith))) fun t' ⟨a, m, k⟩ => ?_
  rw [lo, hi', E.a3, hd, P _ (by omega_arith), P _ (by omega_arith)] at m
  refine ⟨⟨E.write R k (by omega_arith) m, by rw [a, hd, show 128 - t8 - (j + 1) = 127 - t8 - j by omega_arith],
    by rw [k.gpr (by decide), h14], ?_⟩, ?_⟩
  · rw [m, Proof.Rc2.descend_succ]
    exact P.write (by decide) (by omega_arith) _
  · rw [a, hd, ofNat_bne_zero' (by omega_arith)]
    congr 1
    exact decide_eq_decide.mpr (by omega_arith)

end VG.Proof.Rc2.RISCV64

end

end

/-! ### `Rc2.RISCV64.KeyInit`, which only this module used -/

section

/-!
# RC2 on RISC-V: the setup of key expansion

`piInit_run`: PITABLE's doublewords, from immediates, into the working space.
`maskCode_run`: `TM`, chosen by branches on the public `effective_bits mod 8`.
`reduceSetup_run`: `T8` and the index of the reduction.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64
open VG.Impl.Words.RISCV64 (li64)

theorem piInit_steps (u : State) {W : Addr} (hW : u.gpr .a4 = W) (hal : W.toNat % 8 = 0)
    (hw : ∀ k < 32, InRegions u.wr (W + BitVec.ofNat 64 (8 * k)) 8) :
    ∀ n ≤ 32, WP isa (.block ((List.range n).flatMap fun k =>
        li64 .t0 .t1 (Impl.Rc2.piQuad k) ++ ([.store .d .t0 .a4 (8 * k)] : List Instr))) u fun t =>
      (∀ i < n, t.mem.readW (W + BitVec.ofNat 64 (8 * i)) 64 = Impl.Rc2.piQuad i) ∧
      Frame [⟨W, 256⟩] u.mem t.mem ∧ Keep [.t0, .t1] u t := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Keep.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun t ⟨held, F, k⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.t0, .t1] (ByteLoad.li64_ok (s := t) (by decide) (Impl.Rc2.piQuad n)) (by rfl) rfl)
      fun t₁ ⟨e₁, k₁⟩ => ?_
    have a₁ : t₁.gpr .t0 = Impl.Rc2.piQuad n := by rw [e₁]; exact RegUpd.gpr_write_self _ _ _
    have m₁ : t₁.mem = t.mem := by rw [e₁]; rfl
    have h7 : t₁.gpr .a4 = W := by rw [k₁.gpr (by decide), k.gpr (by decide), hW]
    refine WP.mono (WP.keep [] (c := .block [.store .d .t0 .a4 (8 * n)]) (Q := fun t₂ =>
        t₂.mem = t₁.mem.writeW (W + BitVec.ofNat 64 (8 * n)) (Impl.Rc2.piQuad n)) ?_
      (by rfl) rfl) fun t₂ ⟨m₂, k₂⟩ => ⟨fun i hi => ?_, ?_, ?_⟩
    · rrun [h7, a₁, show 8 * n < 2048 by omega_using [hn], Spill.al8 hal (show 8 * n % 8 = 0 by omega_using []),
        show InRegions t₁.wr (W + BitVec.ofNat 64 (8 * n)) 8 by rw [k₁.2.2, k.2.2]; exact hw n (by omega_using [hn])]
    · rw [m₂, m₁]
      by_cases e : i = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep W (by omega_using [e]) (by omega_using [hn, hi]) (by omega_using [hn])) (by decide)]
        exact held i (by omega_using [hi, e])
    · rw [m₂, m₁]; exact F.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn]))
    · exact ((k.trans k₁).trans k₂).mono (by simp)

theorem piInit_run (u : State) {W : Addr} (hW : u.gpr .a4 = W) (hal : W.toNat % 8 = 0)
    (hw : ∀ k < 32, InRegions u.wr (W + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block piInit) u fun t =>
      Proof.Rc2.PiHeld t.mem W ∧ Frame [⟨W, 256⟩] u.mem t.mem ∧ Keep [.t0, .t1] u t :=
  WP.mono (piInit_steps u hW hal hw 32 (Nat.le_refl _)) fun _ ⟨held, F, k⟩ =>
    ⟨fun i hi => by rw [Proof.Rc2.piQuads_length] at hi; rw [held i hi, Proof.Rc2.piQuads_getD hi], F, k⟩

/-- `TM` for `c = effective_bits mod 8`. -/
def maskVal (c : Nat) : Nat := if c = 0 then 255 else 2 ^ c - 1

theorem sub_beq_zero {c k : Nat} (hc : c < 8) (hk : k < 8) :
    (BitVec.ofNat 64 c - BitVec.ofNat 64 k == (0 : BitVec 64)) = decide (c = k) := by
  by_cases h : c = k
  · subst h; simp
  · have : BitVec.ofNat 64 c - BitVec.ofNat 64 k ≠ (0 : BitVec 64) := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_using [hc]), Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_using [hk])] at this
      omega_using [hc, hk, h, this]
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

theorem mask_loop {c₀ : Nat} (hc : c₀ < 8) : ∀ n k, k + n = 7 → ∀ u : State, u.gpr .a6 = BitVec.ofNat 64 c₀ →
    u.gpr .t2 = BitVec.ofNat 64 (if 1 ≤ c₀ ∧ c₀ ≤ k then 2 ^ c₀ - 1 else 255) →
    WP isa ((List.range' k n).foldr (fun c rest => .seq (.block [.addi .t0 .a6 (-((c + 1 : Nat) : Int))])
        (.seq (.ite (.zero .t0) (.block [.li .t2 ((2 ^ (c + 1) - 1 : Nat) : Int)]) (.block [])) rest)) (.block [])) u
      fun t => t.gpr .t2 = BitVec.ofNat 64 (maskVal c₀) ∧ t.mem = u.mem ∧ Keep [.t0, .t2] u t := by
  intro n
  induction n with
  | zero =>
    intro k hk u _ h12
    refine WP.block_nil ⟨?_, rfl, Keep.refl _ _⟩
    rw [h12]; unfold maskVal
    by_cases h : c₀ = 0
    · rw [ite_eq_right (by omega_using [h]), ite_eq_left h]
    · rw [ite_eq_left (by omega_using [hc, hk, h]), ite_eq_right h]
  | succ n ih =>
    intro k hk u h9 h12
    rw [List.range'_succ, List.foldr_cons]
    apply WP.seq
    refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a6 (-((k + 1 : Nat) : Int))]) (Q := fun t =>
        t.gpr .t0 = u.gpr .a6 - BitVec.ofNat 64 (k + 1) ∧ t.mem = u.mem)
      (by rrun [show k + 1 ≤ 2048 by omega_using [hk]]) (by rfl) rfl)
      fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
    apply WP.seq
    have hb : isa.eval (.zero .t0) t₁ = some (decide (c₀ = k + 1)) := by
      rw [Steps.eval_zero, a₁, h9, sub_beq_zero hc (by omega_using [hk])]
    refine WP.ite _ hb (fun ht => ?_) (fun hf => ?_)
    · have e : c₀ = k + 1 := of_decide_eq_true ht
      have hli : 2 ^ (k + 1) - 1 < 2048 := by
        have : 2 ^ (k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_using [hk])
        omega_using [this]
      refine WP.mono (WP.keep [.t2] (c := .block [.li .t2 ((2 ^ (k + 1) - 1 : Nat) : Int)]) (Q := fun t =>
          t.gpr .t2 = BitVec.ofNat 64 (2 ^ (k + 1) - 1) ∧ t.mem = t₁.mem)
        (by rrun [hli])
        (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
      refine WP.mono (ih (k + 1) (by omega_using [hk]) t₂ (by rw [k₂.gpr (by decide), k₁.gpr (by decide), h9])
        (by rw [a₂, ite_eq_left (by omega_using [e]), e])) fun t ⟨a, m, kk⟩ =>
          ⟨a, by rw [m, m₂, m₁], ((k₁.trans k₂).trans kk).mono (by simp)⟩
    · have e : c₀ ≠ k + 1 := of_decide_eq_false hf
      refine WP.block_nil ?_
      refine WP.mono (ih (k + 1) (by omega_using [hk]) t₁ (by rw [k₁.gpr (by decide), h9])
        (by
          rw [k₁.gpr (by decide), h12]
          by_cases h : 1 ≤ c₀ ∧ c₀ ≤ k
          · rw [ite_eq_left h, ite_eq_left (by omega_using [h])]
          · rw [ite_eq_right h, ite_eq_right (by omega_using [e, h])])) fun t ⟨a, m, kk⟩ =>
          ⟨a, by rw [m, m₁], (k₁.trans kk).mono (by simp)⟩

theorem low3 (bits : Nat) (hb : bits < 2 ^ 64) :
    (BitVec.ofNat 64 bits <<< 61) >>> 61 = BitVec.ofNat 64 (bits % 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (show bits % 8 < 2 ^ 64 by omega_using [])]
  omega_using []

theorem maskCode_run (u : State) {bits : Nat} (hb : bits < 2 ^ 64) (h5 : u.gpr .a2 = BitVec.ofNat 64 bits) :
    WP isa maskCode u fun t => t.gpr .t2 = BitVec.ofNat 64 (maskVal (bits % 8)) ∧ t.mem = u.mem ∧
      Keep [.a6, .t0, .t2] u t := by
  unfold maskCode
  apply WP.seq
  refine WP.mono (WP.keep [.a6, .t2] (c := .block [.shift .sll .d .a6 .a2 61, .shift .srl .d .a6 .a6 61, .li .t2 255])
      (Q := fun t => t.gpr .a6 = BitVec.ofNat 64 (bits % 8) ∧ t.gpr .t2 = BitVec.ofNat 64 255 ∧ t.mem = u.mem)
    (by rrun [h5]; exact low3 bits hb) (by rfl) rfl)
    fun t₁ ⟨⟨a₁, b₁, m₁⟩, k₁⟩ => ?_
  rw [List.range_eq_range']
  refine WP.mono (mask_loop (c₀ := bits % 8) (by omega_using []) 7 0 rfl t₁ a₁ (by rw [b₁, ite_eq_right (by omega_using [])]))
    fun t ⟨a, m, k⟩ => ⟨a, by rw [m, m₁], (k₁.trans k).mono (by simp)⟩

theorem maskVal_eq {bits : Nat} : maskVal (bits % 8) = 255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8)) := by
  unfold maskVal
  by_cases h : bits % 8 = 0
  · rw [ite_eq_left h, show 8 + bits - 8 * ((bits + 7) / 8) = 8 by omega_using [h]]
  · rw [ite_eq_right h, show 8 + bits - 8 * ((bits + 7) / 8) = bits % 8 by omega_using [h]]
    have : ∀ c < 8, c ≠ 0 → 2 ^ c - 1 = 255 % 2 ^ c := by decide
    exact this _ (Nat.mod_lt _ (by decide)) h

theorem reduceSetup_run (u : State) {bits : Nat} (hb : bits ≤ 1024) (h5 : u.gpr .a2 = BitVec.ofNat 64 bits) :
    WP isa (.block reduceSetup) u fun t => t.gpr .t4 = BitVec.ofNat 64 ((bits + 7) / 8) ∧
      t.gpr .a5 = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧ t.mem = u.mem ∧ Keep [.a5, .t4] u t := by
  refine WP.mono (WP.keep [.a5, .t4] (c := .block reduceSetup) (Q := fun t =>
      t.gpr .t4 = BitVec.ofNat 64 ((bits + 7) / 8) ∧ t.gpr .a5 = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧
        t.mem = u.mem) ?_ (by rfl) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  have e14 : (BitVec.ofNat 64 bits + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show bits < 2 ^ 64 by omega_using [hb]), Nat.mod_eq_of_lt (show (7 : Nat) < 2 ^ 64 by omega_using []),
      Nat.mod_eq_of_lt (show bits + 7 < 2 ^ 64 by omega_using [hb]), Nat.mod_eq_of_lt (show (bits + 7) / 8 < 2 ^ 64 by omega_using [hb])]
  have e8 : BitVec.ofNat 64 128 - BitVec.ofNat 64 ((bits + 7) / 8) = BitVec.ofNat 64 (128 - (bits + 7) / 8) :=
    Offset.ofNat_sub_ofNat (by omega_using [hb])
  unfold reduceSetup
  rrun [h5, e14, e8]

end VG.Proof.Rc2.RISCV64

end

end


/-!
# RC2 on RISC-V: key expansion

`expandKey_wp`: the schedule at `a3` becomes the expansion of the key at
`a0`, with PITABLE written to the working space at `a4`.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

theorem copyFill_run {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) (hk : key.length = len) (s : State) (E : KEnv K S W len bits key s)
    (h8 : s.gpr .a5 = 0#64) :
    WP isa expandCopyFill s fun t =>
      KEnv K S W len bits key t ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (128 - len)) 128 := by
  have hl := R.hlen
  unfold expandCopyFill
  apply WP.seq
  refine WP.mono (copy_loop R s E h8) fun t₁ ⟨E₁, a₁, P₁⟩ => ?_
  apply WP.seq
  refine WP.mono (WP.keep [.a7] (c := .block [.li .a7 128, .sub .a7 .a5 .a7]) (Q := fun t =>
      t.gpr .a7 = BitVec.ofNat 64 len - BitVec.ofNat 64 128 ∧ t.mem = t₁.mem) (by rrun [a₁])
    (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
  have E₂ := E₁.keep k₂ (by decide) m₂
  have hb : isa.eval (.zero .a7) t₂ = some (decide (len = 128)) := by
    rw [Steps.eval_zero, a₂]
    exact congrArg some (Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith))
  refine WP.ite _ hb (fun ht => WP.block_nil ⟨E₂, ?_⟩) (fun hf => ?_)
  · have e : len = 128 := of_decide_eq_true ht
    rw [m₂, e, Nat.sub_self]; rw [e] at P₁; exact P₁
  · have e : len ≠ 128 := of_decide_eq_false hf
    exact WP.mono (fill_loop R hk (by omega_arith) t₂ E₂ (by rw [k₂.gpr (by decide), a₁]) (by rw [m₂]; exact P₁))
      fun _ ⟨a, _, c⟩ => ⟨a, c⟩

theorem setWidth_ofNat8 (x : Nat) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by decide)

theorem reducePhase_run {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) (hb : 1 ≤ bits ∧ bits ≤ 1024) (s : State) (E : KEnv K S W len bits key s)
    {l : Proof.Rc2.KeyBytes} (P : Proof.Rc2.BytesPrefix s.mem S l 128) :
    WP isa expandReduce s fun t =>
      KEnv K S W len bits key t ∧ Proof.Rc2.BytesPrefix t.mem S
        (Proof.Rc2.descend (Proof.Rc2.reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128 := by
  let t8 := (bits + 7) / 8
  have ht8 : 1 ≤ t8 ∧ t8 ≤ 128 := ⟨by omega_arith, by omega_arith⟩
  unfold expandReduce
  apply WP.seq
  refine WP.mono (reduceSetup_run s hb.2 E.a2) fun t₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  have E₁ := E.keep k₁ (by decide) m₁
  apply WP.seq
  refine WP.mono (maskCode_run t₁ (by omega_arith) E₁.a2) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  have E₂ := E₁.keep k₂ (by decide) m₂
  have h8₂ : t₂.gpr .a5 = BitVec.ofNat 64 (128 - t8) := by rw [k₂.gpr (by decide), b₁]
  have at₂ : t₂.gpr .a3 + t₂.gpr .a5 = S + BitVec.ofNat 64 (128 - t8) := by rw [E₂.a3, h8₂]
  have inS : InRegions t₂.wr (S + BitVec.ofNat 64 (128 - t8)) 1 := by
    rw [E₂.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  apply WP.seq
  refine WP.mono (reduce_run t₂ E₂.pi (by rw [at₂]; obtain ⟨r, hr, hc⟩ := inS; exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [at₂]; exact inS)) fun t₃ ⟨m₃, k₃⟩ => ?_
  have P₂ : Proof.Rc2.BytesPrefix t₂.mem S l 128 := by rw [m₂, m₁]; exact P
  rw [at₂, a₂, setWidth_ofNat8, P₂ _ (by omega_arith), maskVal_eq] at m₃
  have E₃ := E₂.write R (k₃.mono (by simp)) (by omega_arith) m₃
  have P₃ : Proof.Rc2.BytesPrefix t₃.mem S (Proof.Rc2.reduce l bits) 128 := by
    rw [m₃]; exact P₂.write (by decide) (by omega_arith) _
  have h8₃ : t₃.gpr .a5 = BitVec.ofNat 64 (128 - t8) := by rw [k₃.gpr (by decide), h8₂]
  have hz : isa.eval (.zero .a5) t₃ = some (decide (128 - t8 = 0)) := by
    rw [Steps.eval_zero, h8₃, Steps.ofNat_beq_zero (by omega_arith)]
  refine WP.ite _ hz (fun ht => WP.block_nil ⟨E₃, ?_⟩) (fun hf => ?_)
  · have e : 128 - t8 = 0 := of_decide_eq_true ht
    show Proof.Rc2.BytesPrefix t₃.mem S (Proof.Rc2.descend (Proof.Rc2.reduce l bits) t8 (128 - t8)) 128
    rw [e]; exact P₃
  · have e : 128 - t8 ≠ 0 := of_decide_eq_false hf
    exact descend_loop R ⟨ht8.1, by omega_arith⟩ _ t₃ E₃ h8₃
      (by rw [k₃.gpr (by decide), k₂.gpr (by decide), a₁]) P₃

/-- What key expansion may assume. -/
structure KeyPre (s : State) : Prop where
  valid : Spec.Rc2.validKey (s.gpr .a1).toNat (s.gpr .a2).toNat
  rd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩]
  wr : s.wr = [⟨s.gpr .a3, 128⟩, ⟨s.gpr .a4, 512⟩]
  al : (s.gpr .a4).toNat % 8 = 0
  kS : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a3, 128⟩
  kW : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a4, 512⟩
  SW : (⟨s.gpr .a3, 128⟩ : Region).Disjoint ⟨s.gpr .a4, 512⟩

/-- What key expansion guarantees. -/
def KeyPost (s s' : State) : Prop :=
  Spec.Rc2.scheduleAt s'.mem (s.gpr .a3) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (s.gpr .a2).toNat

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.bytesAt m p n).length = n := by
  simp [Spec.Rc2.bytesAt]

theorem expandKey_wp {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let K := s.gpr .a0
  let len := (s.gpr .a1).toNat
  let bits := (s.gpr .a2).toNat
  let S := s.gpr .a3
  let W := s.gpr .a4
  let key := Spec.Rc2.bytesAt s.mem K len
  have hv := h.valid
  unfold Spec.Rc2.validKey at hv
  have R : KRegions K S W len := ⟨⟨hv.1, hv.2.1⟩, h.kS, h.SW⟩
  have wW : ∀ d, d + 8 ≤ 512 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.wr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ hd (by omega_arith)⟩
  unfold expandKey
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (piInit_run s rfl h.al fun k hk => wW _ (by omega_arith)) fun t₁ ⟨held, F₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.a5] (c := .block [.li .a5 0]) (Q := fun t => t.gpr .a5 = 0#64 ∧ t.mem = t₁.mem)
    (by rrun) (by rfl) rfl) fun t₀ ⟨⟨a₀, m₀⟩, k₀⟩ => ?_
  have k01 := k₁.trans k₀
  have E₀ : KEnv K S W len bits key t₀ := by
    refine ⟨k01.gpr (by decide), by rw [k01.gpr (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm,
      by rw [k01.gpr (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm,
      k01.gpr (by decide), ⟨k01.gpr (by decide), h.al, fun j hj => ?_, by rw [m₀]; exact held⟩,
      by rw [k01.2.1]; exact h.rd, by rw [k01.2.2]; exact h.wr, fun c hc => ?_⟩
    · rw [k01.2.1, k01.2.2]
      obtain ⟨r, hr, hc⟩ := wW (8 * j) (by omega_arith)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [m₀, F₁.bytes (R := ⟨K, len⟩) (by simpa using h.kW.sub_right (Region.sub_prefix (show 256 ≤ 512 by decide)))
        (by simp; omega_arith) hc]
      exact (Proof.Rc2.bytesAt_getD _ _ _ _ hc).symm
  have hk : key.length = len := bytesAt_length _ _ _
  apply WP.seq
  refine WP.mono (copyFill_run R hk t₀ E₀ a₀) fun t₂ ⟨E₂, P₂⟩ => ?_
  refine WP.mono (reducePhase_run R ⟨hv.2.2.1, hv.2.2.2⟩ t₂ E₂ P₂) fun t₃ ⟨_, P₃⟩ => ?_
  refine Proof.Rc2.scheduleAt_expanded ?_
  rw [Proof.Rc2.expandBytes_eq, hk]
  exact P₃

end VG.Proof.Rc2.RISCV64

end

end

/-! # Verified RC2 key expansion on RISC-V -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- The key expansion contract as the code sees it. -/
def keyC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let sch : Region := ⟨s.gpr .a3, 128⟩
    let buf : Region := ⟨s.gpr .a4, 512⟩
    s.rd = [key] ∧ s.wr = [sch, buf] ∧ (s.gpr .a4).toNat % 8 = 0 ∧ key.Disjoint sch ∧ key.Disjoint buf ∧
      sch.Disjoint buf ∧ Spec.Rc2.validKey (s.gpr .a1).toNat (s.gpr .a2).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (s.gpr .a3) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (s.gpr .a2).toNat
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-- The registers key expansion writes: no preserved register, nor `ra`. -/
def keyWrites : List Reg := [.a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4]

theorem expandKey_ok (hw : writesOnly keyWrites expandKey = true) (hn : callFree expandKey = true)
    (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨rd, wr, al, kS, kW, SW, valid⟩ := hs
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep keyWrites (expandKey_wp ⟨valid, rd, wr, al, kS, kW, SW⟩) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

end VG.Proof.Rc2.RISCV64

end

end

/-! ### `Rc2.RISCV64.Stream.Checks`, which only this module used -/

section

/-!
# Streaming RC2-CBC on RISCV64: `init`'s checks

`checks_run`: `t0` is zero exactly if the lengths are valid, and otherwise
`a0` holds the code of the first invalid one.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64.Stream

theorem bne_zero_toNat (y : BitVec 64) : (y != (0 : BitVec 64)) = !decide (y.toNat = 0) := by
  have := ofNat_bne_zero' (y.isLt)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem range_bne {x b : Nat} (hx : x < 2 ^ 64) (hb : b < 64) :
    ((BitVec.ofNat 64 x - 1#64) >>> b != (0 : BitVec 64)) = !decide (1 ≤ x ∧ x ≤ 2 ^ b) := by
  rw [bne_zero_toNat]
  congr 1
  obtain hp : 2 ^ b ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega_using [hb])
  have hp1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hx]
  apply decide_eq_decide.mpr
  rw [Nat.div_eq_zero_iff]
  by_cases h : x = 0
  · subst h; omega_using [hp, hp1]
  · rw [show (2 ^ 64 - 1 % 2 ^ 64 + x) % 2 ^ 64 = x - 1 by omega_using [hx, h]]; omega_using [hp1, h]

/-- The code `checks` leaves in `a0` for invalid lengths. -/
def errCode (keyLen bits : Nat) : Nat :=
  if ¬(1 ≤ keyLen ∧ keyLen ≤ 128) then 1 else if ¬(1 ≤ bits ∧ bits ≤ 1024) then 2 else 3

/-- Valid lengths. -/
def valid (keyLen bits ivLen : Nat) : Prop := (1 ≤ keyLen ∧ keyLen ≤ 128) ∧ (1 ≤ bits ∧ bits ≤ 1024) ∧ ivLen = 8

instance (a b c : Nat) : Decidable (valid a b c) := by unfold valid; infer_instance

theorem checks_run (s : State) :
    WP isa checks s fun t => t.mem = s.mem ∧ Keep [.a0, .t0] s t ∧
      (t.gpr .t0 != (0 : BitVec 64)) = !decide (valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat) ∧
      (¬valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat →
        t.gpr .a0 = BitVec.ofNat 64 (errCode (s.gpr .a1).toNat (s.gpr .a2).toNat)) ∧
      (valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat → t.gpr .a0 = s.gpr .a0) := by
  obtain e4 := (BitVec.ofNat_toNat 64 (s.gpr .a1)).trans (BitVec.setWidth_eq _)
  obtain e5 := (BitVec.ofNat_toNat 64 (s.gpr .a2)).trans (BitVec.setWidth_eq _)
  obtain e7 := (BitVec.ofNat_toNat 64 (s.gpr .a4)).trans (BitVec.setWidth_eq _)
  unfold checks
  apply WP.seq
  refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a1 (-1), .shift .srl .d .t0 .t0 7]) (Q := fun t =>
      t.gpr .t0 = (s.gpr .a1 - 1#64) >>> 7 ∧ t.mem = s.mem) (by rrun)
    (by rfl) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  obtain c₁ := range_bne (x := (s.gpr .a1).toNat) (b := 7) (s.gpr .a1).isLt (by decide)
  rw [e4] at c₁
  refine WP.ite _ (by rw [Steps.eval_nonzero, a₁, c₁]) (fun h => ?_) (fun h => ?_)
  · have hk : ¬(1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 128) := by simp at h; omega_using [h]
    refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 1]) (Q := fun t => t.gpr .a0 = 1#64 ∧ t.mem = t₁.mem)
      (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
      ⟨by rw [m, m₁], (k₁.trans k).mono (by simp), ?_, fun _ => ?_, fun hv => absurd hv.1 hk⟩
    · rw [k.gpr (by decide), a₁, c₁]
      simp [valid, hk]
    · rw [a]; simp [errCode, hk]
  · have hk : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 128 := by simpa using h
    apply WP.seq
    refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a2 (-1), .shift .srl .d .t0 .t0 10]) (Q := fun t =>
        t.gpr .t0 = (s.gpr .a2 - 1#64) >>> 10 ∧ t.mem = t₁.mem) (by rrun [k₁.gpr (show Reg.a2 ∉ [Reg.t0] by decide)])
      (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
    obtain c₂ := range_bne (x := (s.gpr .a2).toNat) (b := 10) (s.gpr .a2).isLt (by decide)
    rw [e5] at c₂
    refine WP.ite _ (by rw [Steps.eval_nonzero, a₂, c₂]) (fun h => ?_) (fun h => ?_)
    · have hb : ¬(1 ≤ (s.gpr .a2).toNat ∧ (s.gpr .a2).toNat ≤ 1024) := by simp at h; omega_using [h]
      refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 2]) (Q := fun t => t.gpr .a0 = 2#64 ∧ t.mem = t₂.mem)
        (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
        ⟨by rw [m, m₂, m₁], ((k₁.trans k₂).trans k).mono (by simp), ?_, fun _ => ?_, fun hv => absurd hv.2.1 hb⟩
      · rw [k.gpr (by decide), a₂, c₂]
        simp [valid, hb]
      · rw [a]; simp [errCode, hk, hb]
    · have hb : 1 ≤ (s.gpr .a2).toNat ∧ (s.gpr .a2).toNat ≤ 1024 := by simpa using h
      apply WP.seq
      refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a4 (-8)]) (Q := fun t =>
          t.gpr .t0 = s.gpr .a4 - 8#64 ∧ t.mem = t₂.mem)
        (by rrun [k₂.gpr (show Reg.a4 ∉ [Reg.t0] by decide), k₁.gpr (show Reg.a4 ∉ [Reg.t0] by decide)])
        (by rfl) rfl) fun t₃ ⟨⟨a₃, m₃⟩, k₃⟩ => ?_
      obtain c₃ := sub_bne (x := (s.gpr .a4).toNat) (y := 8) (s.gpr .a4).isLt (by decide)
      rw [e7] at c₃
      refine WP.ite _ (by rw [Steps.eval_nonzero, a₃, c₃]) (fun h => ?_) (fun h => ?_)
      · have hi : (s.gpr .a4).toNat ≠ 8 := by simpa using h
        refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 3]) (Q := fun t => t.gpr .a0 = 3#64 ∧ t.mem = t₃.mem)
          (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
          ⟨by rw [m, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans k).mono (by simp), ?_, fun _ => ?_,
            fun hv => absurd hv.2.2 hi⟩
        · rw [k.gpr (by decide), a₃, c₃]
          simp [valid, hi]
        · rw [a]; simp [errCode, hk, hb]
      · have hi : (s.gpr .a4).toNat = 8 := by simpa using h
        refine WP.block_nil ⟨by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp), ?_, fun hv => ?_,
          fun _ => by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]⟩
        · rw [a₃, c₃]; simp [valid, hk, hb, hi]
        · exact absurd ⟨hk, hb, hi⟩ hv

end VG.Proof.Rc2.RISCV64.Stream

end

end


/-! # Streaming RC2-CBC on RISCV64: `init` -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Stream
open VG.Impl.Rc2.RISCV64.Cbc (mov)

/-- `init`'s buffers: the key at `K` (`L` bytes), the IV at `V` (`N` bytes),
the context at `C` and the working space at `W`. -/
structure InitPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩, ⟨s.gpr .a3, (s.gpr .a4).toNat⟩]
  wr : s.wr = [⟨s.gpr .a5, 144⟩, ⟨s.gpr .a6, 576⟩]
  al : (s.gpr .a6).toNat % 8 = 0
  kC : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a5, 144⟩
  kW : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩
  vC : (⟨s.gpr .a3, (s.gpr .a4).toNat⟩ : Region).Disjoint ⟨s.gpr .a5, 144⟩
  vW : (⟨s.gpr .a3, (s.gpr .a4).toNat⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩
  CW : (⟨s.gpr .a5, 144⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩

theorem expandKey_noFrames : expandKey.noFrames = true := by lit_decide

theorem initArgs_run (t₁ : State) {V C W : Addr} (h6 : t₁.gpr .a3 = V) (h8 : t₁.gpr .a5 = C)
    (h9 : t₁.gpr .a6 = W) (inV₁ : InRegions (t₁.rd ++ t₁.wr) V 8) (inC₁ : InRegions t₁.wr (C + 128#64) 8) :
    WP isa (.block initArgs) t₁ fun t => t.gpr .a3 = C ∧ t.gpr .a4 = W ∧
      t.mem = t₁.mem.writeW (C + 128#64) (t₁.mem.readW V 64) ∧ Keep [.t0, .a7, .t1, .t2, .a3, .a4] t₁ t := by
  unfold initArgs
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Cbc.load64_run (d := .t0) (n := .a3) (p := V) (by decide) (by decide) (by decide) (by decide)
    (by decide) t₁ h6 inV₁) fun u₁ ⟨v₁, mu₁, ku₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2] (c := .block [.addi .t2 .a5 128]) (Q := fun u => u.gpr .t2 = C + 128#64 ∧
      u.mem = u₁.mem) (by rrun [ku₁.gpr (show Reg.a5 ∉ [Reg.t0, .a7, .t1] by decide), h8]) (by rfl) rfl)
    fun u₂ ⟨⟨v₂, mu₂⟩, ku₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Cbc.store64_run (v := .t0) (n := .t2) (p := C + 128#64) (by decide) (by decide) (by decide) u₂ v₂
    (by rw [ku₂.2.2, ku₁.2.2]; exact inC₁)) fun u₃ ⟨mu₃, ku₃⟩ => ?_
  obtain k₃ := (ku₁.trans ku₂).trans ku₃
  obtain g5 : u₃.gpr .a5 = C := by rw [k₃.gpr (by decide), h8]
  obtain g6 : u₃.gpr .a6 = W := by rw [k₃.gpr (by decide), h9]
  refine WP.mono (WP.keep [.a3, .a4] (c := .block [mov .a3 .a5, mov .a4 .a6]) (Q := fun t => t.gpr .a3 = C ∧
      t.gpr .a4 = W ∧ t.mem = u₃.mem) (by rrun [mov, g5, g6]) (by rfl) rfl) fun t ⟨⟨a, b, m⟩, k⟩ =>
      ⟨a, b, ?_, (k₃.trans k).mono (by simp)⟩
  rw [m, mu₃, ku₂.gpr (by decide), v₁, mu₂, mu₁]

theorem initBody_wp (s : State) (h : InitPre s)
    (hv : valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat) :
    WP isa initBody s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      s'.gpr .a0 = 0#64 ∧
      Spec.Rc2.scheduleAt s'.mem (s.gpr .a5) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (s.gpr .a2).toNat ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .a5 + 128) = Spec.Rc2.blockAt s.mem (s.gpr .a3) := by
  obtain ⟨hk, hb, hi⟩ := hv
  obtain ⟨K, hK⟩ : ∃ K, s.gpr .a0 = K := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, s.gpr .a3 = V := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, s.gpr .a5 = C := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, s.gpr .a6 = W := ⟨_, rfl⟩
  obtain hrd := h.rd; have hwr := h.wr; have kC := h.kC; have kW := h.kW; have vC := h.vC; have vW := h.vW
  obtain CW := h.CW; have hal := h.al
  simp only [hK, hV, hC, hW] at hrd hwr kC kW vC vW CW hal
  rw [hK, hC, hV]
  obtain inW : ∀ d, d + 8 ≤ 576 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hwr]; exact ⟨⟨W, 576⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  obtain inC : InRegions s.wr (C + 128) 8 := by
    rw [hwr]; exact ⟨⟨C, 144⟩, by simp, Offset.contains_base C (d := 128) (by omega_arith) (by omega_arith)⟩
  obtain inV : InRegions (s.rd ++ s.wr) V 8 := by
    rw [hrd]; exact ⟨⟨V, (s.gpr .a4).toNat⟩, by simp, by rw [hi]; exact Region.contains_self _ _⟩
  obtain cW : ∀ d, d + 8 ≤ 576 → (⟨W, 576⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := fun d hd =>
    Offset.contains_base W hd (by omega_arith)
  obtain W512 := inW 512 (by decide)
  obtain W520 := inW 520 (by decide)
  -- frames
  obtain slot512 : Region.Sub ⟨W + BitVec.ofNat 64 512, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
  obtain slot520 : Region.Sub ⟨W + BitVec.ofNat 64 520, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
  obtain ivC : Region.Sub ⟨C + 128, 8⟩ ⟨C, 144⟩ := Offset.sub_base C (d := 128) (by omega_arith)
  obtain al512 := Spill.al8 hal (d := 512) (by decide)
  obtain al520 := Spill.al8 hal (d := 520) (by decide)
  unfold initBody withRa
  apply WP.seq
  refine WP.mono (WP.keep [.s7] (c := .block [.store .d .ra .a6 512, .store .d .s7 .a6 520, mov .s7 .a6])
      (Q := fun t => t.gpr .s7 = W ∧
      t.mem = (s.mem.writeW (W + BitVec.ofNat 64 512) (s.gpr .ra)).writeW (W + BitVec.ofNat 64 520) (s.gpr .s7))
    (by rrun [mov, hW, W512, W520, al512, al520]) (by rfl) rfl)
    fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  obtain F₁ : Frame [⟨W, 576⟩] s.mem t₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW (r := ⟨W, 576⟩) (by simp) _ (cW 512 (by decide))).writeW
      (r := ⟨W, 576⟩) (by simp) _ (cW 520 (by decide))
  obtain h6 : t₁.gpr .a3 = V := by rw [k₁.gpr (by decide), hV]
  obtain h8 : t₁.gpr .a5 = C := by rw [k₁.gpr (by decide), hC]
  obtain h9 : t₁.gpr .a6 = W := by rw [k₁.gpr (by decide), hW]
  obtain inV₁ : InRegions (t₁.rd ++ t₁.wr) V 8 := by rw [k₁.2.1, k₁.2.2]; exact inV
  obtain inC₁ : InRegions t₁.wr (C + 128#64) 8 := by rw [k₁.2.2]; exact inC
  apply WP.seq
  apply WP.seq
  refine WP.mono (initArgs_run t₁ h6 h8 h9 inV₁ inC₁) fun t₂ ⟨a6, a7, m₂, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  obtain h3 : t₂.gpr .a0 = K := by rw [k12.gpr (by decide), hK]
  obtain h4 : t₂.gpr .a1 = s.gpr .a1 := k12.gpr (by decide)
  obtain h5 : t₂.gpr .a2 = s.gpr .a2 := k12.gpr (by decide)
  obtain C128 : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  obtain W512r : Region.Sub ⟨W, 512⟩ ⟨W, 576⟩ := Region.sub_prefix (by decide)
  apply WP.seq
  refine WP.call (k := keyC) (expandKey_ok (by lit_decide) (by lit_decide)) (rd := [⟨K, (s.gpr .a1).toNat⟩]) (wr := [⟨C, 128⟩, ⟨W, 512⟩]) ?_ ?_ ?_
    (fun t₃ rd₃ wr₃ _ F₃ P₃ _ post₃ => ?_) expandKey_noFrames
  · simp only [keyC, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr]
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h3, h4, h5, a6, a7]
    exact ⟨rfl, rfl, hal, kC.sub_right C128, kW.sub_right W512r, (CW.sub_left C128).sub_right W512r, hk.1, hk.2,
      hb.1, hb.2⟩
  · rw [k12.2.1, k12.2.2, hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨C, 144⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨W, 576⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · rw [k12.2.2, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨W, 576⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  -- after the call
  refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 0]) (Q := fun t => t.gpr .a0 = 0#64 ∧ t.mem = t₃.mem)
    (by rrun) (by rfl) rfl) fun t₄ ⟨⟨a3, m₄⟩, k₄⟩ => ?_
  obtain h31 : t₄.gpr .s7 = W := by rw [k₄.gpr (by decide), P₃ _ (by decide), k₂.gpr (by decide), a₁]
  obtain F₂ : Frame [⟨C, 144⟩, ⟨W, 576⟩] s.mem t₂.mem := by
    rw [m₂]
    exact (F₁.mono (by simp)).writeW (r := ⟨C, 144⟩) (by simp) _ (Offset.contains_base C (d := 128) (by omega_arith) (by omega_arith))
  -- the slots, apart from the context and the called function's working space
  obtain slot : ∀ d, 512 ≤ d → d + 8 ≤ 576 → t₄.mem.readW (W + BitVec.ofNat 64 d) 64 = t₁.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    intro d hd hd'
    obtain sd : Region.Sub ⟨W + BitVec.ofNat 64 d, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
    rw [m₄, F₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact (CW.sub_left C128).symm.sub_left sd
      · exact Offset.disjoint_base W (by omega_arith) (by omega_arith)) (by decide), m₂,
      Mem.readW_writeW_sep (((CW.sub_left ivC).symm.sub_left sd).sep (Region.contains_self _ _)
        (Region.contains_self _ _)) (by decide)]
  obtain e512 : t₄.mem.readW (W + 512#64) 64 = s.gpr .ra := by
    rw [slot 512 (by decide) (by decide), m₁, Mem.readW_writeW_sep (Offset.sep W (by omega_arith) (by omega_arith) (by omega_arith))
      (by decide), Mem.readW_writeW_self64]
  obtain e520 : t₄.mem.readW (W + 520#64) 64 = s.gpr .s7 := by
    rw [slot 520 (by decide) (by decide), m₁, Mem.readW_writeW_self64]
  obtain rw₄ : t₄.rd = s.rd ∧ t₄.wr = s.wr := ⟨by rw [k₄.2.1, rd₃, k12.2.1], by rw [k₄.2.2, wr₃, k12.2.2]⟩
  obtain in512 : InRegions (t₄.rd ++ t₄.wr) (W + 512#64) 8 := by
    rw [rw₄.1, rw₄.2]; obtain ⟨r, hr, hc⟩ := W512; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain in520 : InRegions (t₄.rd ++ t₄.wr) (W + 520#64) 8 := by
    rw [rw₄.1, rw₄.2]; obtain ⟨r, hr, hc⟩ := W520; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep [.ra, .s7] (c := .block [.load .d .ra .s7 512, .load .d .s7 .s7 520])
      (Q := fun t => t.gpr .s7 = s.gpr .s7 ∧ t.gpr .ra = s.gpr .ra ∧ t.mem = t₄.mem)
    (by rrun [h31, e512, e520, in512, in520, al512, al520]) (by rfl) rfl)
    fun t₅ ⟨⟨a31, lr₅, m₅⟩, k₅⟩ => ⟨fun r hr => ?_, lr₅, by rw [k₅.gpr (by decide), a3], ?_, ?_⟩
  · by_cases h31' : r = .s7
    · subst h31'; exact a31
    · have hn : r ∉ [Reg.ra, .s7, .t0, .a7, .t1, .t2, .a3, .a4] := by revert hr h31'; revert r; decide
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [k₅.gpr (by simp [hn]), k₄.gpr (by simp; intro e; subst e; revert hr; decide), P₃ r hr,
        k12.gpr (by simp [hn])]
  · have hB : Spec.Rc2.bytesAt t₂.mem K (s.gpr .a1).toNat = Spec.Rc2.bytesAt s.mem K (s.gpr .a1).toNat :=
      Proof.Rc2.bytesAt_frame F₂ K _ (by omega_arith) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact kC
        · exact kW)
    have := post₃
    simp only [keyC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem] at this
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), a6, h3, h4, h5, hB] at this
    rw [m₅, m₄]; exact this
  · have hiv : Spec.Rc2.blockAt t₃.mem (C + 128#64) = Spec.Rc2.blockAt t₂.mem (C + 128#64) :=
      Proof.Rc2.blockAt_frame F₃ _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact Offset.disjoint_base C (d := 128) (by omega_arith) (by omega_arith)
        · exact (CW.sub_left ivC).sub_right W512r)
    obtain hV₁ : Spec.Rc2.blockAt t₁.mem V = Spec.Rc2.blockAt s.mem V :=
      Proof.Rc2.blockAt_frame F₁ V (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r rfl
        rw [← hi]; exact vW)
    show Spec.Rc2.blockAt t₅.mem (C + 128#64) = _
    rw [m₅, m₄, hiv, m₂, Proof.Rc2.blockAt_store64, ← Proof.Rc2.blockAt_read64, hV₁]

/-- `init`'s postcondition. -/
def initPost (s s' : State) : Prop :=
  ∀ direction, match Spec.Rc2.initWithEffectiveBits
      (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
      (Spec.Rc2.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) direction (s.gpr .a2).toNat with
    | .ok c => BitVec.setWidth 32 (s'.gpr .a0) = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .a5) direction 0 = c
    | .error e => (BitVec.setWidth 32 (s'.gpr .a0)).toNat = e.code

theorem init_wp (s : State) (h : InitPre s) :
    WP isa init s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      initPost s s' := by
  unfold init
  apply WP.seq
  refine WP.mono (checks_run s) fun t₁ ⟨m₁, k₁, c₁, e₁, v₁⟩ => ?_
  obtain g : ∀ r, r ∉ [Reg.a0, .t0] → t₁.gpr r = s.gpr r := fun r hr => k₁.gpr hr
  obtain g4 := g .a1 (by decide); have g5 := g .a2 (by decide); have g6 := g .a3 (by decide)
  obtain g7 := g .a4 (by decide); have g8 := g .a5 (by decide); have g9 := g .a6 (by decide)
  refine WP.ite _ (by rw [Steps.eval_nonzero, c₁]) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hv : ¬valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat := by simpa using hb
    refine ⟨fun r hr => k₁.gpr (by revert hr; revert r; decide), k₁.gpr (by decide), ?_⟩
    refine Proof.Rc2.init_post_error ?_ hv
    rw [e₁ hv]
    unfold errCode
    split
    · rfl
    · split <;> rfl
  · have hv : valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat := by simpa using hb
    obtain g3 := v₁ hv
    obtain h' : InitPre t₁ := by
      obtain ⟨rd, wr, al, kC, kW, vC, vW, CW⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [k₁.2.1, k₁.2.2, g3, g4, g6, g7, g8, g9] <;>
        with_reducible assumption
    refine WP.mono (initBody_wp t₁ h' (by rw [g4, g5, g7]; exact hv)) fun s' ⟨P, L, r3, S, V⟩ =>
      ⟨fun r hr => by rw [P r hr, k₁.gpr (by revert hr; revert r; decide)], by rw [L, k₁.gpr (by decide)], ?_⟩
    rw [g3, g4, g5, g8, m₁] at S
    rw [g6, g8, m₁] at V
    exact Proof.Rc2.init_post hv.1 hv.2.1 hv.2.2 (by rw [r3]; rfl) S V

end VG.Proof.Rc2.RISCV64.Stream

end

end

/-!
# Verified streaming RC2-CBC on RISC-V

`init` meets the shared contract with their working space as
an argument (`Proof.Rc2.cbcInitScratchContract`),
and, in a frame that allocates the working space and zeroes it after the code
(`Verified.stackScratchWiped`), the contract of `Spec/Rc2/Contract.lean`. The
code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64.Stream

/-- `init`'s contract as the code sees it. -/
def initC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let iv : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let ctx : Region := ⟨s.gpr .a5, 144⟩
    let scr : Region := ⟨s.gpr .a6, 576⟩
    s.rd = [key, iv] ∧ s.wr = [ctx, scr] ∧ (s.gpr .a6).toNat % 8 = 0 ∧ key.Disjoint ctx ∧ key.Disjoint scr ∧
      iv.Disjoint ctx ∧ iv.Disjoint scr ∧ ctx.Disjoint scr
  post s s' := initPost s s'
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
    s₁.sp = s₂.sp

theorem init_ok (s : State) (hs : initC.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initC.post s s' := by
  obtain ⟨rd, wr, al, kC, kW, vC, vW, CW⟩ := hs
  obtain ⟨t, s', he, ⟨hp, hl, hq⟩, _, _, hsp⟩ := WP.rdwr (init_wp s ⟨rd, wr, al, kC, kW, vC, vW, CW⟩)
  exact ⟨t, s', he, ⟨hp, hsp, hl⟩, hq⟩

theorem agree {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
      s₁.sp = s₂.sp) {pre : State → Prop} :
    ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6]) s₁ s₂ := by
  intro s₁ s₂ _ _ hp
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, psp⟩ := h s₁ s₂ hp
  refine ⟨psp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem init_ct : ConstantTime isa initC.pre initC.pub init :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6])
    (agree fun _ _ h => h) (by taint_decide)

def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a3 => 0x2000 | .a5 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

theorem init_verified : Verified RISCV64.target init (Proof.Rc2.cbcInitScratchContract RISCV64.abi) := by
  refine Verified.of_correct (k := initC) init_ok init_ct ?_
  sig_implies [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, RISCV64.abi,
    RISCV64.argRegs,
    initC, initPost] [initSat] using initSat

end VG.Proof.Rc2.RISCV64.Stream

end

end

/-!
# Streaming RC2-CBC on RISC-V, with its working space on the stack

`init` runs its code, proved with the working space as an
argument (`Verified.lean`), in a frame of 608 bytes that allocates it
(`Verified.stackScratchWiped`), and zero its 576 bytes before returning.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64.Stream

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract RISCV64.abi 608).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, RISCV64.abi,
    RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 init)
      (Spec.Rc2.cbcInitContract RISCV64.abi 608) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64) (n := 72)
    (post := Spec.Rc2.cbcInitPost RISCV64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 608) (words := 72)
    init_verified (by decide) (by decide) (by decide) (Proof.Rc2.cbcInitPostOut_local _) initFrameSat_pre

end VG.Proof.Rc2.RISCV64.Stream

end

end

/-!
# Rc2 on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`Impl.Rc2.RISCV64.Fn`, the functions as emitted), which clears the
caller-saved registers and the stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/Rc2/X86_64/Scrub.lean`).

Every function instead clears only the runs of doublewords that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs
(`Impl.Scrub.RISCV64.scrubSel`). Their code wipes most of
its own scratch space, which leaves few such doublewords, or none.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Scrub

open VG.Spec.Rc2 VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem cbcInitOut (stack : Nat) : PostOut (Spec.Rc2.cbcInitContract RISCV64.abi stack) (Spec.Rc2.cbcInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcInitPostOut_local _)

theorem cbcEncryptChainedOut (stack : Nat) : PostOut (Spec.Rc2.cbcEncryptChainedContract RISCV64.abi stack) (Spec.Rc2.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcEncChainedPostOut_local (pb := 64))

theorem cbcDecryptChainedOut (stack : Nat) : PostOut (Spec.Rc2.cbcDecryptChainedContract RISCV64.abi stack) (Spec.Rc2.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcDecChainedPostOut_local (pb := 64))

/-! ## The functions as emitted

Each theorem states that a function as emitted (`Impl.Rc2.RISCV64.Fn`) meets its
contract in constant time and returns without secret residue
(`VerifiedScrubbed`, by `RISCV64.Scrub.verifiedScrubbedAll`, or
`verifiedScrubbedSel` for the selective cleanup, whose residue analysis the
kernel evaluates here): what its registration binds. -/

/-- `Spec.Rc2.cbcInitApi` as emitted (`Impl.Rc2.RISCV64.Fn.cbcInit`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcInit_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Rc2.RISCV64.Fn.cbcInit
      (Spec.Rc2.cbcInitContract RISCV64.abi 608) 32 :=
  verifiedScrubbedSel (api := Spec.Rc2.cbcInitApi) (W := 608) (rb := 32)
    { code := Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 Impl.Rc2.RISCV64.Stream.init
      verified := Proof.Rc2.RISCV64.Stream.init_framed }
    _ [] (cbcInitOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `Spec.Rc2.cbcEncryptChainedApi` as emitted (`Impl.Rc2.RISCV64.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Rc2.RISCV64.Fn.cbcEncryptChained
      (Spec.Rc2.cbcEncryptChainedContract RISCV64.abi 512) 0 :=
  verifiedScrubbedSel (api := Spec.Rc2.cbcEncryptChainedApi) (W := 512) (rb := 0)
    { code := Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.encrypt
      verified := Proof.Rc2.RISCV64.Cbc.encryptChained_framed }
    _ [] (cbcEncryptChainedOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `Spec.Rc2.cbcDecryptChainedApi` as emitted (`Impl.Rc2.RISCV64.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Rc2.RISCV64.Fn.cbcDecryptChained
      (Spec.Rc2.cbcDecryptChainedContract RISCV64.abi 512) 0 :=
  verifiedScrubbedSel (api := Spec.Rc2.cbcDecryptChainedApi) (W := 512) (rb := 0)
    { code := Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.decrypt
      verified := Proof.Rc2.RISCV64.Cbc.decryptChained_framed }
    _ [] (cbcDecryptChainedOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

end VG.Proof.Rc2.RISCV64.Scrub
