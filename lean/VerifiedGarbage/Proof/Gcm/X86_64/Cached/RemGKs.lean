module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemMask
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
public import VerifiedGarbage.Impl.Aes.X86_64.VaesZ
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group
import VerifiedGarbage.Proof.Framework.X86_64.MaskedPrefix
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Framework.X86_64.ZFrameBlock
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Spec.Gcm

/-! ### `Gcm.X86_64.Cached.RemGHash`, which this module and modules that import it used -/

section

/-! ### `Gcm.X86_64.Cached.RemGXor`, which this module and modules that import it used -/

section

/-! ### `Gcm.X86_64.Cached.RemQuadK`, which this module and modules that import it used -/

section

/-!
# The blocks after the last group, through a mask

What the masked loads of the blocks after the last group share
(`RemGXor.lean`, `RemGHash.lean`): a masked load's result in a register
(`setZv`, `zlane_setZv`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Proof.Gcm.X86_64.StitchZ (restZ ldAcc ldAcc_ok)
open VG.Proof.Aes.X86_64.VaesZ (zmm_lane)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Spec.Gcm (Block blockAt)

/-- The lanes of a 512-bit value written to a register. -/
theorem zlane_setZv (s : State) (d : XReg) (v : BitVec 512) {l : Nat} (hl : l < 4) :
    (s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128) (v.extractLsb' 384 128)).zlane d l =
      v.extractLsb' (128 * l) 128 := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
  simp only [ite_true]
  exact pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hl

/-- A masked load's result, in a register. -/
abbrev setZv (s : State) (d : XReg) (v : BitVec 512) : State :=
  s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128) (v.extractLsb' 384 128)

end VG.Proof.Gcm.X86_64.StitchZH

end

end

/-!
# The blocks after the last group, added to their keystream in registers

`xorG_ok`: `StitchZH.xorG src rs j` adds the data at `src + 64 j` … to the
keystream registers `rs` and stores them to `rdx + 64 j` …, the last
register through the mask of its `c` blocks: each block stored is the data
block and the keystream added, and is what its register's lane, byte-
reversed, holds, which the hash then takes.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZH (xorG)
open VG.Proof.Aes.X86_64.VaesZ (zmm_lane blockAt_writeW_lane load512_lane)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt)

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  show s.gpr b + BitVec.ofInt 64 (d : Int) = _
  rw [BitVec.ofInt_natCast]

/-- A register XORed with the 64 bytes at `src + d` and stored to `rdx + d`. -/
theorem xor1G_ok (src : Reg) (b : XReg) (d : Nat) (s : State) (hb : b ≠ .xmm13)
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 64)
    (hinD : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 d) 64) :
    WP isa (.block [.vmovdqu32Load .xmm13 (at_ src d), .zop (.zbin .vpxord b b .xmm13),
        .vmovdqu32Store (at_ .rdx d) b]) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 d) v) ∧
      (∀ l < 4, blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) =
        blockAt s.mem (s.gpr src + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.zlane b l) revMask) ∧
      (∀ l < 4, XBinOp.eval .pshufb (s'.zlane b l) revMask =
        blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm13 → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let a := s.gpr .rdx + BitVec.ofNat 64 d
  let as := s.gpr src + BitVec.ofNat 64 d
  let v := s.mem.readW as 512
  let s₁ := setZv s .xmm13 v
  let s₂ := (ZOp.zbin .vpxord b b .xmm13).exec s₁
  have l₁ : ∀ l < 4, s₁.zlane .xmm13 l = s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [zlane_setZv _ _ _ hl]; exact load512_lane _ _ hl
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load512, ea_at', hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdqu32Store (at_ .rdx d) b) s₂ = some (s₂.setMem (s.mem.writeW a (s₂.zmm b))) := by
    simp only [isa, exec, State.store512_eq, ea_at', s₂, s₁, ZOp.exec_gpr,
      State.setZ_gpr, ZOp.exec_wr, State.setZ_wr, ZOp.exec_mem, State.setZ_mem, hinD, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  have z₂ : ∀ l < 4, s₂.zlane b l = s.zlane b l ^^^ s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, l₁ l hl]
      rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
      simp only [hb, ite_false, VG.Proof.Aes.X86_64.AesNi.eval_pxor]
  have bD : ∀ l < 4, blockAt (s.mem.writeW a (s₂.zmm b)) (a + BitVec.ofNat 64 (16 * l)) =
      XBinOp.eval .pshufb (s₂.zlane b l) revMask := fun l hl => by
    rw [blockAt_writeW_lane _ _ _ hl, zmm_lane _ _ hl]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁],
    fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [bD l hl, z₂ l hl, pshufb_rev_xor, BitVec.xor_comm, ← blockAt_eq]
  · simp only [State.setMem_mem, State.setMem_zlane]
    exact (bD l hl).symm
  · simp [s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl, h1, h2]

/-- A register XORed with the first `c` blocks at `src + d` and its `c` low
lanes stored to `rdx + d`, through the mask in `r10`. -/
theorem xorK1_ok (src : Reg) (b : XReg) (d : Nat) (s : State) {c : Nat} (hc : c ≤ 4) (hb : b ≠ .xmm13)
    (hk : State.qOn (s.gpr .r10) = List.range (2 * c))
    (hbk : ∀ j < 8, (s.gpr .r10).getLsbD j = decide (j < 2 * c))
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) (16 * c))
    (hinD : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 d) (16 * c)) :
    WP isa (.block [.kLoad .r10 .xmm13 (at_ src d), .zop (.zbin .vpxord b b .xmm13),
        .kStore (at_ .rdx d) .r10 b]) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 d) (v.setWidth (128 * c))) ∧
      (∀ l < c, blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) =
        blockAt s.mem (s.gpr src + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.zlane b l) revMask) ∧
      (∀ l < c, XBinOp.eval .pshufb (s'.zlane b l) revMask =
        blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm13 → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let a := s.gpr .rdx + BitVec.ofNat 64 d
  let as := s.gpr src + BitVec.ofNat 64 d
  obtain ⟨v, ev, lv⟩ := State.loadMasked512_prefix (s := s) (a := as) hc hk hbk hinS
  let s₁ := setZv s .xmm13 v
  let s₂ := (ZOp.zbin .vpxord b b .xmm13).exec s₁
  let m₃ := s.mem.writeW a ((s₂.zmm b).setWidth (128 * c))
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec]; rw [ea_at', ev]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨{ s₂ with mem := m₃ }, by
    simp only [isa, exec]
    rw [ea_at', show s₂.gpr .rdx + BitVec.ofNat 64 d = a from rfl, show s₂.gpr .r10 = s.gpr .r10 from rfl,
      State.storeMasked512_prefix (s := s₂) hc hk (show InRegions s₂.wr a (16 * c) from hinD)]
    rfl, WP.block_nil ?_⟩
  have z₂ : ∀ l < c, s₂.zlane b l = s.zlane b l ^^^ s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, zlane_zbin _ _ _ _ _ _ (show l < 4 by omega_using [hc, hl]), ite_true, ZBinOp.sse]
      rw [zlane_setZv _ _ _ (by omega_using [hc, hl]), lv l (by omega_using [hc, hl]), ite_eq_left hl, State.zlane_setZ_ne _ hb _ _ _ _ (by omega_using [hc, hl])]
      simp only [VG.Proof.Aes.X86_64.AesNi.eval_pxor]
  have bD : ∀ l < c, blockAt m₃ (a + BitVec.ofNat 64 (16 * l)) =
      XBinOp.eval .pshufb (s₂.zlane b l) revMask := fun l hl => by
    rw [blockAt_eq]
    have e := readW_writeW_inside s.mem a ((s₂.zmm b).setWidth (128 * c)) (k := 16 * l) (n := 16)
      (by omega_using [hl]) (by omega_using [hc])
    rw [show 8 * 16 = 128 by rfl] at e
    rw [e, show 8 * (16 * l) = 128 * l by omega_using []]
    have e2 : ((s₂.zmm b).setWidth (128 * c)).extractLsb' (128 * l) 128 = (s₂.zmm b).extractLsb' (128 * l) 128 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
      rw [decide_eq_true (show 128 * l + i < 128 * c by omega_using [hl, hi]), Bool.true_and]
    rw [e2, zmm_lane _ _ (by omega_using [hc, hl])]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁],
    fun r h1 h2 l hl => ?_⟩
  · show blockAt m₃ _ = _
    rw [bD l hl, z₂ l hl, pshufb_rev_xor, BitVec.xor_comm, ← blockAt_eq]
  · exact (bD l hl).symm
  · show s₂.zlane r l = _
    simp [s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl, h1, h2]

/-- The registers `rs` XORed with the data at `src + 64 j` … and stored to
`rdx + 64 j` …, the last through the mask of its `c` blocks: of the
`4 (|rs| - 1) + c` blocks, each one stored is the data and the keystream
added, and what its register's lane holds, byte-reversed. -/
theorem xorG_ok (src : Reg) : ∀ (rs : List XReg) (j : Nat) (s : State) {c : Nat}, rs ≠ [] → rs.Nodup →
    .xmm13 ∉ rs → c ≤ 4 →
    State.qOn (s.gpr .r10) = List.range (2 * c) → (∀ i < 8, (s.gpr .r10).getLsbD i = decide (i < 2 * c)) →
    InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 (64 * j)) (64 * (rs.length - 1) + 16 * c) →
    InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (64 * j)) (64 * (rs.length - 1) + 16 * c) →
    (∀ n q', q' < n / 4 → n < 4 * (rs.length - 1) + c →
      Region.Disjoint ⟨s.gpr src + BitVec.ofNat 64 (16 * (4 * j + n)), 16⟩
        ⟨s.gpr .rdx + BitVec.ofNat 64 (64 * (j + q')), 64⟩) →
    j + rs.length ≤ 4 →
    WP isa (.block (xorG src rs j)) s fun s' =>
      (∀ n < 4 * (rs.length - 1) + c, blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (4 * j + n))) =
        blockAt s.mem (s.gpr src + BitVec.ofNat 64 (16 * (4 * j + n))) ^^^
          XBinOp.eval .pshufb (s.zlane (rs.getD (n / 4) .xmm0) (n % 4)) revMask) ∧
      (∀ n < 4 * (rs.length - 1) + c, XBinOp.eval .pshufb (s'.zlane (rs.getD (n / 4) .xmm0) (n % 4)) revMask =
        blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (4 * j + n)))) ∧
      Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (64 * j), 64 * (rs.length - 1) + 16 * c⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ rs → r ≠ .xmm13 → ∀ l < 4, s'.zlane r l = s.zlane r l)
  | [], _, _, _, h, _, _, _, _, _, _, _, _, _ => absurd rfl h
  | [b], j, s, c, _, _, h13, hc, hk, hb, hinS, hinD, _, hw => by
    have hb13 : b ≠ .xmm13 := fun h => h13 (h ▸ List.mem_singleton_self _)
    simp only [List.length_singleton, Nat.sub_self, Nat.mul_zero, Nat.zero_add] at hinS hinD ⊢
    refine WP.mono (xorK1_ok src b (64 * j) s hc hb13 hk hb hinS hinD)
      fun s' ⟨⟨v, m'⟩, b', z', g', rd', wr', k'⟩ => ⟨fun n hn => ?_, fun n hn => ?_, ?_, g', rd', wr',
        fun r hr h13' l hl => k' r (fun h => hr (h ▸ List.mem_singleton_self _)) h13' l hl⟩
    · have := b' n hn
      rw [Offset.add_add, Offset.add_add, show 64 * j + 16 * n = 16 * (4 * j + n) by omega_arith] at this
      rw [this, show n / 4 = 0 by omega_arith, show n % 4 = n by omega_arith]; rfl
    · have := z' n hn
      rw [Offset.add_add, show 64 * j + 16 * n = 16 * (4 * j + n) by omega_arith] at this
      rw [← this, show n / 4 = 0 by omega_arith, show n % 4 = n by omega_arith]; rfl
    · rw [m']
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (by rw [show 128 * c / 8 = 16 * c by omega_arith]; exact Region.contains_self _ _)
  | b :: b₂ :: bs, j, s, c, _, hnd, h13, hc, hk, hb, hinS, hinD, hsep, hw => by
    have hb13 : b ≠ .xmm13 := fun h => h13 (h ▸ List.mem_cons_self)
    have hbs : b ∉ b₂ :: bs := (List.nodup_cons.mp hnd).1
    have h13' : .xmm13 ∉ b₂ :: bs := fun h => h13 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hinS hinD hsep hw ⊢
    rw [show xorG src (b :: b₂ :: bs) j = ([.vmovdqu32Load .xmm13 (at_ src (64 * j)), .zop (.zbin .vpxord b b .xmm13),
      .vmovdqu32Store (at_ .rdx (64 * j)) b] : List Instr) ++ xorG src (b₂ :: bs) (j + 1) from rfl,
      WP.block_append_iff]
    have hlen : 64 ≤ 64 * (bs.length + 1 + 1 - 1) + 16 * c := by omega_arith
    have hn64 : 64 * (bs.length + 1 + 1 - 1) + 16 * c < 2 ^ 64 := by omega_arith
    refine WP.mono (xor1G_ok src b (64 * j) s hb13
      (by have := CallLay.inRegions_sub (off := 0) (l := 64) hinS (by omega_arith) hn64
          rwa [show s.gpr src + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 0 = s.gpr src + BitVec.ofNat 64 (64 * j)
            from BitVec.add_zero _] at this)
      (by have := CallLay.inRegions_sub (off := 0) (l := 64) hinD (by omega_arith) hn64
          rwa [show s.gpr .rdx + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 0 = s.gpr .rdx + BitVec.ofNat 64 (64 * j)
            from BitVec.add_zero _] at this))
      fun s₁ ⟨⟨v, m₁⟩, b₁, z₁, g₁, rd₁, wr₁, k₁⟩ => ?_
    have hk₁ : State.qOn (s₁.gpr .r10) = List.range (2 * c) := by rw [g₁]; exact hk
    have hb₁ : ∀ i < 8, (s₁.gpr .r10).getLsbD i = decide (i < 2 * c) := by rw [g₁]; exact hb
    have eoff : ∀ x : Nat, BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 x = BitVec.ofNat 64 (64 * j + x) := fun x => by
      rw [BitVec.ofNat_add_ofNat]
    refine WP.mono (xorG_ok src (b₂ :: bs) (j + 1) s₁ (List.cons_ne_nil _ _) (List.nodup_cons.mp hnd).2 h13' hc hk₁ hb₁
      (by
        rw [rd₁, wr₁, g₁]
        have := CallLay.inRegions_sub (off := 64) (l := 64 * ((b₂ :: bs).length - 1) + 16 * c) hinS
          (by simp only [List.length_cons]; omega_arith) hn64
        rwa [Offset.add_add, show 64 * j + 64 = 64 * (j + 1) by omega_arith] at this)
      (by
        rw [wr₁, g₁]
        have := CallLay.inRegions_sub (off := 64) (l := 64 * ((b₂ :: bs).length - 1) + 16 * c) hinD
          (by simp only [List.length_cons]; omega_arith) hn64
        rwa [Offset.add_add, show 64 * j + 64 = 64 * (j + 1) by omega_arith] at this)
      (fun n q' hq hn => by
        rw [g₁, show 4 * (j + 1) + n = 4 * j + (n + 4) by omega_arith, show j + 1 + q' = j + (q' + 1) by omega_arith]
        exact hsep (n + 4) (q' + 1) (by omega_arith) (by simp only [List.length_cons] at hn ⊢; omega_arith))
      (by simp only [List.length_cons] at hw ⊢; omega_arith))
      fun s' ⟨b', z', f', g', rd', wr', k'⟩ => ?_
    simp only [List.length_cons] at b' z' f'
    rw [g₁] at b' z' f'
    -- The first register's blocks, which the later writes keep.
    have keep0 : ∀ n < 4, blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (4 * j + n))) =
        blockAt s₁.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (4 * j + n))) := fun n hn =>
      blockAt_frame f' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    -- The later registers' data, which the first write keeps.
    have keepS : ∀ n, 4 ≤ n → n < 4 * (bs.length + 1) + c →
        blockAt s₁.mem (s.gpr src + BitVec.ofNat 64 (16 * (4 * j + n))) =
          blockAt s.mem (s.gpr src + BitVec.ofNat 64 (16 * (4 * j + n))) := fun n h4 hn => by
      rw [m₁]
      apply Stitch.blockAt_writeW_sep' (R := ⟨s.gpr .rdx + BitVec.ofNat 64 (64 * j), 64⟩) _ rfl
      have := hsep n 0 (by omega_arith) (by omega_arith)
      rwa [Nat.add_zero] at this
    refine ⟨fun n hn => ?_, fun n hn => ?_, ?_, by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁],
      fun r hr h13'' l hl => ?_⟩
    · by_cases h4 : n < 4
      · rw [keep0 n h4]
        have := b₁ n h4
        rw [Offset.add_add, Offset.add_add, show 64 * j + 16 * n = 16 * (4 * j + n) by omega_arith] at this
        rw [this, show n / 4 = 0 by omega_arith, show n % 4 = n by omega_arith]; rfl
      · have := b' (n - 4) (by omega_arith)
        rw [show 4 * (j + 1) + (n - 4) = 4 * j + n by omega_arith, show (n - 4) / 4 = n / 4 - 1 by omega_arith,
          show (n - 4) % 4 = n % 4 by omega_arith] at this
        rw [this, keepS n (by omega_arith) (by omega_arith)]
        have hq : n / 4 = (n / 4 - 1) + 1 := by omega_arith
        rw [hq, List.getD_cons_succ, Nat.add_sub_cancel, k₁ _ (fun h => by
          have hm : (b₂ :: bs).getD (n / 4 - 1) .xmm0 ∈ b₂ :: bs := by
            rw [← List.getElem_eq_getD (h := by simp only [List.length_cons]; omega_arith)]
            exact List.getElem_mem _
          exact hbs (h ▸ hm)) (fun h => by
          have hm : (b₂ :: bs).getD (n / 4 - 1) .xmm0 ∈ b₂ :: bs := by
            rw [← List.getElem_eq_getD (h := by simp only [List.length_cons]; omega_arith)]
            exact List.getElem_mem _
          exact h13' (h ▸ hm)) _ (by omega_arith)]
    · by_cases h4 : n < 4
      · rw [keep0 n h4, show n / 4 = 0 by omega_arith, show n % 4 = n by omega_arith, List.getD_cons_zero,
          k' b hbs hb13 _ (by omega_arith)]
        have := z₁ n h4
        rw [Offset.add_add, show 64 * j + 16 * n = 16 * (4 * j + n) by omega_arith] at this
        exact this
      · have := z' (n - 4) (by omega_arith)
        rw [show 4 * (j + 1) + (n - 4) = 4 * j + n by omega_arith, show (n - 4) / 4 = n / 4 - 1 by omega_arith,
          show (n - 4) % 4 = n % 4 by omega_arith] at this
        rw [show n / 4 = (n / 4 - 1) + 1 by omega_arith, List.getD_cons_succ]
        exact this
    · have F1 : Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (64 * j), 64 * (bs.length + 1 + 1 - 1) + 16 * c⟩]
          s.mem s₁.mem := by
        rw [m₁]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)
      exact F1.trans (f'.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩)
    · rw [k' r (fun h => hr (List.mem_cons_of_mem _ h)) h13'' l hl,
        k₁ r (fun h => hr (h ▸ List.mem_cons_self)) h13'' l hl]

end VG.Proof.Gcm.X86_64.StitchZH

end

end

/-! ### `Gcm.X86_64.Cached.RemGLanes`, which this module and modules that import it used -/

section

/-!
# The lanes of the blocks after the last group, as a group

In the masked group (`StitchZH.remG`), block `j` of the last `r` is lane
`j mod 4` of register `j / 4`, and each lane's products add up over the
registers in order: `laneAccG`, whose four lanes' reduced products add up to
`GHASH` over the `r` blocks for the powers of a group's table (`RemOkG`,
which `StitchZ/OkP.lean` proves, `remZG`). Lanes after the `r`
blocks are multiplied by zero, and add nothing (`laneAccG_pad`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB)
open VG.Spec.Gcm (Block ghashFrom)

/-- The products in lane `l` of the first `n` blocks `X` with their powers
`T`, block `j` in lane `j mod 4`, `y` added to the first. -/
def laneAccG (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (l : Nat) : Nat → Prod
  | 0 => Prod.zero
  | n + 1 => if n % 4 = l then (laneAccG X T y l n).acc ((if n = 0 then y else 0) ^^^ X n) (T n)
      else laneAccG X T y l n

theorem laneAccG_congr {X X' : Nat → Block} {T T' : Nat → BitVec 128} (y : Block) (l : Nat) :
    ∀ n, (∀ j < n, X j = X' j) → (∀ j < n, T j = T' j) → laneAccG X T y l n = laneAccG X' T' y l n
  | 0, _, _ => rfl
  | n + 1, hX, hT => by
    simp only [laneAccG]
    rw [laneAccG_congr y l n (fun j hj => hX j (by omega_using [hj])) (fun j hj => hT j (by omega_using [hj])), hX n (by omega_using []),
      hT n (by omega_using [])]

/-- The four blocks of register `q`, one to each lane. -/
theorem laneAccG_quad (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (q : Nat) {l : Nat} (hl : l < 4) :
    laneAccG X T y l (4 * q + 4) =
      (laneAccG X T y l (4 * q)).acc ((if 4 * q + l = 0 then y else 0) ^^^ X (4 * q + l)) (T (4 * q + l)) := by
  have h0 : (4 * q) % 4 = 0 := by omega_using []
  have h1 : (4 * q + 1) % 4 = 1 := by omega_using []
  have h2 : (4 * q + 2) % 4 = 2 := by omega_using []
  have h3 : (4 * q + 3) % 4 = 3 := by omega_using []
  rw [show 4 * q + 4 = 4 * q + 3 + 1 from rfl]
  rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
  simp only [laneAccG, h0, h1, h2, h3, Nat.add_zero, ite_true, ite_false,
    show ¬ ((3 : Nat) = 0) by decide, show ¬ ((2 : Nat) = 0) by decide,
    show ¬ ((1 : Nat) = 0) by decide, show ¬ ((3 : Nat) = 1) by decide, show ¬ ((2 : Nat) = 1) by decide,
    show ¬ ((0 : Nat) = 1) by decide, show ¬ ((3 : Nat) = 2) by decide, show ¬ ((1 : Nat) = 2) by decide,
    show ¬ ((0 : Nat) = 2) by decide, show ¬ ((2 : Nat) = 3) by decide, show ¬ ((1 : Nat) = 3) by decide,
    show ¬ ((0 : Nat) = 3) by decide]

/-- Blocks multiplied by zero add nothing: past `r`, with powers zero there,
the lanes are those of the first `r`. -/
theorem laneAccG_pad (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (l r : Nat) :
    ∀ n, r ≤ n → laneAccG X (fun j => if j < r then T j else 0) y l n = laneAccG X T y l r
  | 0, h => by
    rw [show r = 0 by omega_using [h]]; rfl
  | n + 1, h => by
    by_cases hn : n + 1 = r
    · subst hn
      exact laneAccG_congr y l (n + 1) (fun _ _ => rfl) fun j hj => by simp [hj]
    · have ih := laneAccG_pad X T y l r n (by omega_using [h, hn])
      simp only [laneAccG]
      rw [ih, ite_eq_right (show ¬ n < r by omega_using [h, hn])]
      split <;> [exact Prod.acc_zero_right _ _; rfl]

/-- What the products of the last `r` blocks with the powers of a group, in
the lanes of the masked group, add up to, each lane's reduced: `GHASH` over
the `r` blocks (`StitchZ/OkP.lean` proves it of the powers the setup stores,
`H'¹⁶⁻ᵐ` at `16 m`). -/
def RemOkG (H : Block) (P : Nat → Nat → Block) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 15 → ∀ (X : Nat → Block) (y : Block),
    (reduceB (laneAccG X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y 0 r) ^^^
        reduceB (laneAccG X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y 2 r)) ^^^
      (reduceB (laneAccG X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y 1 r) ^^^
        reduceB (laneAccG X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y 3 r)) =
      ghashFrom H y ((List.range r).map X)

end VG.Proof.Gcm.X86_64.StitchZH

end

end

/-!
# The blocks after the last group, hashed in registers

`hashG_ok`: `StitchZH.hashG rs j` multiplies the lanes of the registers
`rs`, byte-reversed (`Y` added to the first block), by the powers at
`rax + 64 j` …, the last register's loaded through the mask of its `c`
blocks, so that its other lanes are multiplied by zero: each lane's products
are `laneAccG`'s, block `n` in lane `n mod 4`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH (hash1 hashG)
open VG.Proof.Gcm.X86_64.StitchZ (ldInit ldAcc ldAcc_ok)
open VG.Proof.Aes.X86_64.VaesZ (load512_lane)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block)

/-- The SSE block of `hash1 b j` in each lane. -/
def hashSse (b : XReg) (j : Nat) : List Instr :=
  .xop (.bin .movdqa .xmm7 b) ::
    (if j = 0 then ([.xop (.bin .pshufb .xmm7 .xmm0), .xop (.bin .pxor .xmm7 .xmm2)] : List Instr) ++ ldInit.tail
      else ldAcc false)

theorem lane_hash1 {b : XReg} (hb : b ∈ aregs) (j : Nat) : zlaneSseBlock (hash1 b j) = some (hashSse b j) := by
  simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at hb
  by_cases hj : j = 0 <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [hash1, hashSse, hj, ↓reduceIte] <;> rfl

theorem hashSse_ok {b : XReg} (hb : b ∈ aregs) (j : Nat) (t : State) :
    WP isa (.block (hashSse b j)) t fun t' =>
      prod t' = (if j = 0 then Prod.zero else prod t).acc
        ((if j = 0 then t.xmm .xmm2 else 0) ^^^ XBinOp.eval .pshufb (t.xmm b) (t.xmm .xmm0)) (t.xmm .xmm12) ∧
      Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at hb
  by_cases hj : j = 0
  · apply WP.of_runBlock
    rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [hashSse, hj, ↓reduceIte, ldInit, List.tail_cons, List.cons_append, List.nil_append, reduceCtorEq,
      runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm, Pclmul.eval_pxor, eval_movdqa,
      Option.some.injEq, exists_eq_left'] <;>
    refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩ <;>
    first
    | (simp only [prod, Prod.acc, Prod.zero, Stitch.zero_xor_b, reduceCtorEq, ↓reduceIte,
        BitVec.xor_comm (t.xmm .xmm2)]; done)
    | (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
       simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false])
  · simp only [hashSse, hj, ↓reduceIte]
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, WP.mono (ldAcc_ok false _) fun t' ⟨p', o'⟩ => ⟨?_, ?_⟩⟩
    · rw [p']
      rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [XOp.exec, State.setXmm, eval_movdqa, prod, reduceCtorEq, ↓reduceIte, Bool.false_eq_true]
    · have o₁ : Only [.xmm7] t (XOp.exec (.bin .movdqa .xmm7 b) t) :=
        ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr => by
          simp only [List.mem_singleton] at hr
          simp only [XOp.exec, State.setXmm, hr, ite_false]⟩
      exact (o₁.trans o').weaken fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h | h <;> simp only [h, true_or, or_true]

/-- The products of register `b`'s lanes, byte-reversed (`Y` added if
`j = 0`), with the powers in `zmm12`, written (`j = 0`) or added. -/
theorem hash1_ok {b : XReg} (hb : b ∈ aregs) (j : Nat) (t : State) (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask) :
    WP isa (.block (hash1 b j)) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = (if j = 0 then Prod.zero else prod (t.zproj l)).acc
        ((if j = 0 then t.zlane .xmm2 l else 0) ^^^ XBinOp.eval .pshufb (t.zlane b l) revMask) (t.zlane .xmm12 l)) ∧
      ZFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  refine WP.mono (WP.zlanes (lane_hash1 hb j) fun l _ => hashSse_ok hb j (t.zproj l))
    fun t' ⟨hk, hq⟩ => ⟨fun l hl => ?_, ⟨hk.gpr, hk.mem, hk.rd, hk.wr, fun r hr l hl => ?_⟩⟩
  · rw [(hq l hl).1]; simp only [State.zproj_xmm, h0 l hl]
  · have := (hq l hl).2.xmm r hr
    simpa only [State.zproj_xmm] using this

/-- The 64 bytes at `b + d` in `zmm` `x`. -/
theorem ld512_ok (x : XReg) (b : Reg) (d : Nat) (t : State)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr b + BitVec.ofNat 64 d) 64) :
    WP isa (.block [.vmovdqu32Load x (at_ b d)]) t fun t' =>
      (∀ l < 4, t'.zlane x l = t.mem.readW (t.gpr b + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) 128) ∧
      ZFrame [x] t t' := by
  rw [WP.block_cons_iff]
  refine ⟨setZv t x (t.mem.readW (t.gpr b + BitVec.ofNat 64 d) 512),
    by simp only [isa, exec, State.load512, ea_at', hin, ite_true, Option.map_some], WP.block_nil ⟨fun l hl => ?_,
      ⟨rfl, rfl, rfl, rfl, fun r hr l hl => State.zlane_setZ_ne _ (fun h => hr (List.mem_singleton.mpr h)) _ _ _ _ hl⟩⟩⟩
  rw [zlane_setZv _ _ _ hl]; exact load512_lane _ _ hl

/-- The `c` blocks at `b + d` in `zmm` `x`, through the mask in `r10`, and
zero in its other lanes. -/
theorem ld512K_ok (x : XReg) (b : Reg) (d : Nat) (t : State) {c : Nat} (hc : c ≤ 4)
    (hk : State.qOn (t.gpr .r10) = List.range (2 * c))
    (hbk : ∀ j < 8, (t.gpr .r10).getLsbD j = decide (j < 2 * c))
    (hin : InRegions (t.rd ++ t.wr) (t.gpr b + BitVec.ofNat 64 d) (16 * c)) :
    WP isa (.block [.kLoad .r10 x (at_ b d)]) t fun t' =>
      (∀ l < 4, t'.zlane x l =
        if l < c then t.mem.readW (t.gpr b + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) 128 else 0) ∧
      ZFrame [x] t t' := by
  obtain ⟨v, ev, lv⟩ := State.loadMasked512_prefix (s := t) (a := t.gpr b + BitVec.ofNat 64 d) hc hk hbk hin
  rw [WP.block_cons_iff]
  refine ⟨setZv t x v, by simp only [isa, exec]; rw [ea_at', ev]; rfl, WP.block_nil ⟨fun l hl => ?_,
      ⟨rfl, rfl, rfl, rfl, fun r hr l hl => State.zlane_setZ_ne _ (fun h => hr (List.mem_singleton.mpr h)) _ _ _ _ hl⟩⟩⟩
  rw [zlane_setZv _ _ _ hl, lv l hl]

/-- A register's products, as the lanes' of the next four blocks. -/
theorem hashStep_eq {X : Nat → Block} {T : Nat → BitVec 128} {y : Block} {l j : Nat} (hl : l < 4) (p : Prod)
    (y2 x2 pw : BitVec 128) (hp : j ≠ 0 → p = laneAccG X T y l (4 * j)) (hy : y2 = if l = 0 then y else 0)
    (hx : X (4 * j + l) = x2) (hT : T (4 * j + l) = pw) :
    (if j = 0 then Prod.zero else p).acc ((if j = 0 then y2 else 0) ^^^ x2) pw = laneAccG X T y l (4 * (j + 1)) := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega_arith, laneAccG_quad X T y j hl, hx, hT]
  by_cases hj : j = 0
  · subst hj
    simp only [ite_true, hy, Nat.mul_zero, Nat.zero_add]
    rfl
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hj), ite_eq_right_iff.mpr (fun h => absurd h hj), ← hp hj,
      ite_eq_right_iff.mpr (fun h => absurd (show j = 0 by omega_arith) hj)]

/-- The registers `rs`, from the `j`-th, hashed with the powers at
`rax + 64 j` …, the last's through the mask of its `c` blocks: the lanes'
products are those of blocks `4 j` … `4 (j + |rs|)`, block `n` lane `n mod
4` of its register byte-reversed, with power `T n`, zero after the
`4 (|rs| - 1) + c`. -/
theorem hashG_ok : ∀ (rs : List XReg) (j : Nat) (t : State) {c : Nat} (X : Nat → Block) (T : Nat → BitVec 128)
    (y : Block), rs ≠ [] → (∀ b ∈ rs, b ∈ aregs) → rs.length ≤ 4 → c ≤ 4 →
    State.qOn (t.gpr .r10) = List.range (2 * c) → (∀ i < 8, (t.gpr .r10).getLsbD i = decide (i < 2 * c)) →
    (∀ l < 4, t.zlane .xmm0 l = revMask) → (∀ l < 4, t.zlane .xmm2 l = if l = 0 then y else 0) →
    InRegions (t.rd ++ t.wr) (t.gpr .rax + BitVec.ofNat 64 (64 * j)) (64 * (rs.length - 1) + 16 * c) →
    (∀ n < 4 * rs.length, X (4 * j + n) = XBinOp.eval .pshufb (t.zlane (rs.getD (n / 4) .xmm0) (n % 4)) revMask) →
    (∀ n < 4 * rs.length, T (4 * j + n) =
      if n < 4 * (rs.length - 1) + c then t.mem.readW (t.gpr .rax + BitVec.ofNat 64 (16 * (4 * j + n))) 128
      else 0) →
    (j ≠ 0 → ∀ l < 4, prod (t.zproj l) = laneAccG X T y l (4 * j)) →
    WP isa (.block (hashG rs j)) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = laneAccG X T y l (4 * (j + rs.length))) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t'
  | [], _, _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _ => absurd rfl h
  | [b], j, t, c, X, T, y, _, hrs, _, hc, hk, hbk, h0, h2, hin, hX, hT, hP => by
    have hb := hrs b (List.mem_singleton_self _)
    have hb12 : b ≠ .xmm12 := by simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with
      rfl | rfl | rfl | rfl <;> decide
    simp only [List.length_singleton, Nat.sub_self, Nat.mul_zero, Nat.zero_add] at hin hX hT ⊢
    rw [show hashG [b] j = ([.kLoad .r10 .xmm12 (at_ .rax (64 * j))] : List Instr) ++ hash1 b j from rfl,
      WP.block_append_iff]
    refine WP.mono (ld512K_ok .xmm12 .rax (64 * j) t hc hk hbk hin) fun t₁ ⟨l₁, f₁⟩ => ?_
    refine WP.mono (hash1_ok hb j t₁ fun l hl => by rw [f₁.zlane _ (by decide) l hl, h0 l hl])
      fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, (f₁.comp f').mono (by decide)⟩
    rw [p' l hl]
    refine hashStep_eq hl _ _ _ _ (fun hj => ?_) ?_ ?_ ?_
    · rw [← hP hj l hl]
      simp only [prod, State.zproj_xmm, f₁.zlane .xmm8 (by decide) l hl, f₁.zlane .xmm9 (by decide) l hl,
        f₁.zlane .xmm10 (by decide) l hl]
    · rw [f₁.zlane _ (by decide) l hl, h2 l hl]
    · rw [hX l (by omega_arith), f₁.zlane _ (fun h => hb12 (List.mem_singleton.mp h)) l hl,
        show l / 4 = 0 by omega_arith, show l % 4 = l by omega_arith]; rfl
    · rw [hT l (by omega_arith), l₁ l hl, Offset.add_add, show 64 * j + 16 * l = 16 * (4 * j + l) by omega_arith]
  | b :: b₂ :: bs, j, t, c, X, T, y, _, hrs, hlen, hc, hk, hbk, h0, h2, hin, hX, hT, hP => by
    have hb := hrs b List.mem_cons_self
    have hb12 : b ≠ .xmm12 := by simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with
      rfl | rfl | rfl | rfl <;> decide
    simp only [List.length_cons] at hin hX hT hlen ⊢
    have hn64 : 64 * (bs.length + 1 + 1 - 1) + 16 * c < 2 ^ 64 := by omega_arith
    rw [show hashG (b :: b₂ :: bs) j = ([.vmovdqu32Load .xmm12 (at_ .rax (64 * j))] : List Instr) ++ hash1 b j ++
      hashG (b₂ :: bs) (j + 1) from rfl, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (ld512_ok .xmm12 .rax (64 * j) t
      (by have := CallLay.inRegions_sub (off := 0) (l := 64) hin (by omega_arith) hn64
          rwa [BitVec.add_zero] at this)) fun t₁ ⟨l₁, f₁⟩ => ?_
    refine WP.mono (hash1_ok hb j t₁ fun l hl => by rw [f₁.zlane _ (by decide) l hl, h0 l hl])
      fun t₂ ⟨p₂, f₂⟩ => ?_
    have f₁₂ := f₁.comp f₂
    have keep : ∀ r, r ∉ [XReg.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] → ∀ l < 4, t₂.zlane r l = t.zlane r l :=
      fun r hr l hl => f₁₂.zlane r (by simpa only [List.cons_append, List.nil_append] using hr) l hl
    have kreg : ∀ r ∈ b :: b₂ :: bs, ∀ l < 4, t₂.zlane r l = t.zlane r l := fun r hr l hl =>
      keep r (by
        have := hrs r hr
        simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl | rfl | rfl <;> decide) l hl
    have step : ∀ l < 4, prod (t₂.zproj l) = laneAccG X T y l (4 * (j + 1)) := fun l hl => by
      rw [p₂ l hl]
      refine hashStep_eq hl _ _ _ _ (fun hj => ?_) ?_ ?_ ?_
      · rw [← hP hj l hl]
        simp only [prod, State.zproj_xmm, f₁.zlane .xmm8 (by decide) l hl, f₁.zlane .xmm9 (by decide) l hl,
          f₁.zlane .xmm10 (by decide) l hl]
      · rw [f₁.zlane _ (by decide) l hl, h2 l hl]
      · rw [hX l (by omega_arith), f₁.zlane _ (fun h => hb12 (List.mem_singleton.mp h)) l hl,
          show l / 4 = 0 by omega_arith, show l % 4 = l by omega_arith]; rfl
      · rw [hT l (by omega_arith), ite_eq_left (by omega_arith), l₁ l hl, Offset.add_add,
          show 64 * j + 16 * l = 16 * (4 * j + l) by omega_arith]
    refine WP.mono (hashG_ok (b₂ :: bs) (j + 1) t₂ X T y (List.cons_ne_nil _ _)
      (fun r hr => hrs r (List.mem_cons_of_mem _ hr)) (by simp only [List.length_cons]; omega_arith) hc
      (by rw [f₁₂.gpr]; exact hk) (by rw [f₁₂.gpr]; exact hbk)
      (fun l hl => by rw [keep _ (by decide) l hl, h0 l hl]) (fun l hl => by rw [keep _ (by decide) l hl, h2 l hl])
      (by
        rw [f₁₂.rd, f₁₂.wr, f₁₂.gpr]
        have := CallLay.inRegions_sub (off := 64) (l := 64 * ((b₂ :: bs).length - 1) + 16 * c) hin
          (by simp only [List.length_cons]; omega_arith) hn64
        rwa [Offset.add_add, show 64 * j + 64 = 64 * (j + 1) by omega_arith] at this)
      (fun n hn => by
        simp only [List.length_cons] at hn
        rw [show 4 * (j + 1) + n = 4 * j + (n + 4) by omega_arith, hX (n + 4) (by omega_arith),
          show (n + 4) / 4 = n / 4 + 1 by omega_arith, show (n + 4) % 4 = n % 4 by omega_arith, List.getD_cons_succ,
          kreg _ (by
            rw [← List.getElem_eq_getD (h := by simp only [List.length_cons]; omega_arith)]
            exact List.mem_cons_of_mem _ (List.getElem_mem _)) _ (by omega_arith)])
      (fun n hn => by
        simp only [List.length_cons] at hn ⊢
        rw [show 4 * (j + 1) + n = 4 * j + (n + 4) by omega_arith, hT (n + 4) (by omega_arith), f₁₂.mem, f₁₂.gpr]
        by_cases h : n < 4 * (bs.length + 1 - 1) + c
        · rw [ite_eq_left (by omega_arith), ite_eq_left h]
        · rw [ite_eq_right (by omega_arith), ite_eq_right h])
      (fun _ => step)) fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, ?_⟩
    · rw [p' l hl, show j + 1 + (b₂ :: bs).length = j + (bs.length + 1 + 1) by simp only [List.length_cons]; omega_arith]
    · exact (f₁₂.comp f').mono (by decide)

end VG.Proof.Gcm.X86_64.StitchZH

end

end

/-! ### `Gcm.X86_64.Cached.Ks`, which this module and modules that import it used -/

section

/-!
# The keys of the rounds of the blocks after the last group

What encrypting the counters of the blocks after the last group needs: the
key schedule, as the rounds need it, from a state that has not written it
(`keys_of`), and `ctrsZ` keeping the cached keys (`ctrsZ_keeps`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp pp cb dp dR pR cR bAddr ciph sch in_sub_int)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys zmm_lane blockAt_writeW_lane)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Proof.Gcm.X86_64.StitchZ (AInv aregs_ok)
open VG.Spec.Gcm (Block blockAt inc32)

/-- The key schedule is not in the data, the working space or the counter. -/
theorem sch_frame3 {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {m : Mem} (hf : Frame [dR s₀, pR s₀, cR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m (kp s₀) (16 * (nr s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nr s₀ + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine hf.bytes (R := ⟨kp s₀, 16 * (nr s₀ + 1)⟩) (fun r hr => ?_)
    (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega_using [hn]) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.d_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.p_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.c_k.symm.sub_left (Region.sub_prefix hn)

/-- The key schedule, as the rounds need it, from a state that has not
written it. -/
theorem keys_of {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {t : State} (h1 : t.gpr .rdi = kp s₀) (h2 : t.rd = s₀.rd)
    (h3 : t.wr = s₀.wr) (h4 : Frame [dR s₀, pR s₀, cR s₀] s₀.mem t.mem) : Keys (nr s₀) (sch s₀) t :=
  ⟨by rw [h1, sch_frame3 hp h4], by rcases hp.rounds with h | h | h <;> omega_using [h],
    fun j hj => by
      rw [h2, h3, h1]
      exact Stitch.in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega_using [hj, h])⟩

theorem ctrsZ_keeps (c m i : XReg) : ∀ regs : List XReg,
    (Impl.Aes.X86_64.VaesZ.ctrsZ c m i regs).all Instr.keepsH = true
  | [] => rfl
  | _ :: bs => by
    simp only [Impl.Aes.X86_64.VaesZ.ctrsZ, List.all_append, ctrsZ_keeps c m i bs, Bool.and_true]; rfl

end VG.Proof.Gcm.X86_64.StitchZH

end

end

/-!
# The blocks after the last group, as a masked group: after the rounds

`remMaskG_ok`: from `r9 = 16 + r`, `StitchZH.remMaskG` puts in `r10` the mask
of the last register's `c = (r - 1) mod 4 + 1` blocks (`maskG_ok`: its
quadwords are the first `2 c`). `tailG_ok`: then `xorG`, `hashG` and `fin`
add the data at `src` to the keystream in the registers and store the `r`
blocks to `rdx`, and put in `Y` the four lanes' products of the blocks
stored, reduced and added (`laneAccG`, the powers after the `r` blocks
zero: `laneAccG_pad`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (fin)
open VG.Impl.Gcm.X86_64.StitchZH (remMaskG xorG hashG)
open VG.Proof.Gcm.X86_64.StitchZ (aregs_ok fin_ok)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt inc32)
open VG.Proof.Gcm.X86_64.Stitch (SPre nr kp pp cb dR pR cR ciph sch)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq)

/-- The masks of one to four blocks: their first `2 c` quadwords. -/
theorem maskG_ok : ∀ c < 5, 1 ≤ c →
    State.qOn (BitVec.ofNat 64 (4 ^ c - 1)) = List.range (2 * c) ∧
      ∀ j < 8, (BitVec.ofNat 64 (4 ^ c - 1)).getLsbD j = decide (j < 2 * c) := by decide

/-- The mask of the last register's `(r - 1) mod 4 + 1` blocks, in `r10`. -/
theorem remMaskG_ok (s : State) {r : Nat} (hr1 : 1 ≤ r) (hr : r < 16) (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) :
    WP isa remMaskG s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (4 ^ ((r - 1) % 4 + 1) - 1) ∧ (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (WP.mono (testR9_ok s 1) fun t ⟨z, g, l, m, rd, wr⟩ => ?_)
  have zt : t.zf = some (decide (r % 2 = 0)) := by rw [z, h9, test1 r hr]
  refine WP.ite (decide (r % 2 = 0)) (by simp only [eval, zt]) (fun h => ?_) (fun h => ?_)
  all_goals refine WP.seq (WP.mono (testR9_ok t 2) fun t₂ ⟨z₂, g₂, l₂, m₂, rd₂, wr₂⟩ => ?_)
  all_goals have zt₂ : t₂.zf = some (decide (r % 4 < 2)) := by rw [z₂, g, h9, test2 r hr]
  all_goals refine WP.ite (decide (r % 4 < 2)) (by simp only [eval, zt₂]) (fun h' => ?_) (fun h' => ?_)
  all_goals refine WP.mono (movR10_ok t₂ _) fun t' ⟨a, b, c, d, e, f⟩ => ⟨?_, fun q hq => by rw [b q hq, g₂, g],
    fun x l' => by rw [c, l₂, l], by rw [d, m₂, m], by rw [e, rd₂, rd], by rw [f, wr₂, wr]⟩
  all_goals rw [a]
  all_goals simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h h'
  · rw [show (r - 1) % 4 + 1 = 4 by omega_arith]; decide
  · rw [show (r - 1) % 4 + 1 = 2 by omega_arith]; decide
  · rw [show (r - 1) % 4 + 1 = 1 by omega_arith]; decide
  · rw [show (r - 1) % 4 + 1 = 3 by omega_arith]; decide

/-- The registers of a group of `k`. -/
theorem aregs_take (k : Nat) : (aregs.take k).Nodup ∧ .xmm13 ∉ aregs.take k ∧ ∀ b ∈ aregs.take k, b ∈ aregs := by
  obtain ⟨hnd, h13, _⟩ := aregs_ok
  exact ⟨hnd.sublist (List.take_sublist _ _), fun h => h13 (List.mem_of_mem_take h),
    fun _ h => List.mem_of_mem_take h⟩

/-- After the rounds of a group of `k` registers for the last `r` blocks:
the data at `src` (`S`) added to their keystream (`K`), the `r` blocks
stored to `rdx` (`A`), and `Y` the four lanes' products of them with the
powers at `rax` (`W`), from `Y` in `xmm2`, reduced and added. -/
theorem tailG_ok (src : Reg) (hsrc : src ≠ .r10) {k r : Nat} (hk4 : k ≤ 4) (hr1 : 1 ≤ r) (hr15 : r ≤ 15) (hrk : r ≤ 4 * k)
    (hkr : 4 * k < r + 4) {t : State} {A S W : Addr} {K D T : Nat → Block} {y : Block}
    (h9 : t.gpr .r9 = BitVec.ofNat 64 (16 + r)) (hA : t.gpr .rdx = A) (hS : t.gpr src = S) (hW : t.gpr .rax = W)
    (hks : ∀ n < r, XBinOp.eval .pshufb (t.zlane ((aregs.take k).getD (n / 4) .xmm0) (n % 4)) revMask = K n)
    (hD : ∀ n < r, blockAt t.mem (S + BitVec.ofNat 64 (16 * n)) = D n)
    (hT : ∀ n < r, t.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128 = T n)
    (hinS : InRegions (t.rd ++ t.wr) S (16 * r)) (hinD : InRegions t.wr A (16 * r))
    (hinW : InRegions (t.rd ++ t.wr) W (16 * r))
    (hsep : ∀ n q', q' < n / 4 → n < r →
      Region.Disjoint ⟨S + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A + BitVec.ofNat 64 (64 * q'), 64⟩)
    (hWA : ∀ n < r, Region.Disjoint ⟨W + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A, 16 * r⟩)
    (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask) (h1 : ∀ l < 4, t.zlane .xmm1 l = poly)
    (h2 : ∀ l < 4, t.zlane .xmm2 l = if l = 0 then y else 0) :
    WP isa (.seq remMaskG (.block (xorG src (aregs.take k) 0 ++ hashG (aregs.take k) 0 ++ fin))) t fun t' =>
      (∀ n < r, blockAt t'.mem (A + BitVec.ofNat 64 (16 * n)) = D n ^^^ K n) ∧
      Frame [⟨A, 16 * r⟩] t.mem t'.mem ∧
      t'.zlane .xmm2 0 =
        (reduceB (laneAccG (fun n => D n ^^^ K n) T y 0 r) ^^^ reduceB (laneAccG (fun n => D n ^^^ K n) T y 2 r)) ^^^
          (reduceB (laneAccG (fun n => D n ^^^ K n) T y 1 r) ^^^ reduceB (laneAccG (fun n => D n ^^^ K n) T y 3 r)) ∧
      (∀ l, 1 ≤ l → l < 4 → t'.zlane .xmm2 l = 0) ∧
      (∀ q, q ≠ .r10 → t'.gpr q = t.gpr q) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) →
        ∀ l < 4, t'.zlane x l = t.zlane x l) := by
  obtain ⟨hnd, h13, hin⟩ := aregs_take k
  have hlen : (aregs.take k).length = k := by simp [aregs]; omega_arith
  have hk1 : 1 ≤ k := by omega_arith
  have hc : 4 * ((aregs.take k).length - 1) + ((r - 1) % 4 + 1) = r := by rw [hlen]; omega_arith
  have hc16 : 64 * ((aregs.take k).length - 1) + 16 * ((r - 1) % 4 + 1) = 16 * r := by rw [hlen]; omega_arith
  obtain ⟨mq, mb⟩ := maskG_ok ((r - 1) % 4 + 1) (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (remMaskG_ok t hr1 (by omega_arith) h9) fun t₁ ⟨a₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  have e0 : ∀ a : Addr, a + BitVec.ofNat 64 (64 * 0) = a := fun a => BitVec.add_zero a
  refine WP.mono (xorG_ok src (aregs.take k) 0 t₁ (c := (r - 1) % 4 + 1) (by
      intro h; rw [h] at hlen; simp at hlen; omega_arith) hnd h13 (by omega_arith)
      (by rw [a₁]; exact mq) (by rw [a₁]; exact mb)
      (by rw [rd₁, wr₁, g₁ _ hsrc, hS, e0, hc16]; exact hinS)
      (by rw [wr₁, g₁ _ (by decide), hA, e0, hc16]; exact hinD)
      (fun n q' hq hn => by
        rw [g₁ _ hsrc, g₁ _ (by decide), hS, hA, Nat.mul_zero, Nat.zero_add, Nat.zero_add]
        exact hsep n q' hq (by omega_arith))
      (by rw [hlen]; omega_arith)) fun t₂ ⟨b₂, z₂, f₂, g₂, rd₂, wr₂, k₂⟩ => ?_
  rw [hc, g₁ _ (by decide), hA] at b₂ z₂
  rw [hc16, g₁ _ (by decide), hA, e0] at f₂
  rw [g₁ _ hsrc, hS] at b₂
  simp only [Nat.mul_zero, Nat.zero_add] at b₂ z₂
  -- The lanes of the registers, now the blocks stored, and the powers.
  let X' : Nat → Block := fun n => XBinOp.eval .pshufb (t₂.zlane ((aregs.take k).getD (n / 4) .xmm0) (n % 4)) revMask
  let T₀ : Nat → BitVec 128 := fun n => t₂.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128
  have hT₀ : ∀ n < r, T₀ n = T n := fun n hn => by
    show t₂.mem.readW _ 128 = _
    rw [f₂.readW (r := ⟨W + BitVec.ofNat 64 (16 * n), 16⟩) (Region.contains_self _ _)
      (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hWA n hn) (by decide), m₁]
    exact hT n hn
  have hX' : ∀ n < r, X' n = D n ^^^ K n := fun n hn => by
    show XBinOp.eval .pshufb _ revMask = _
    rw [z₂ n hn, b₂ n hn, m₁, hD n hn]
    congr 1
    rw [← hks n hn, l₁]
  have hW₂ : t₂.gpr .rax = W := by rw [g₂, g₁ _ (by decide), hW]
  have keep₂ : ∀ x, x ∉ aregs.take k → x ≠ .xmm13 → ∀ l < 4, t₂.zlane x l = t.zlane x l := fun x hx h13' l hl => by
    rw [k₂ x hx h13' l hl, l₁]
  have nA : ∀ x, x ∉ aregs → x ∉ aregs.take k := fun x hx h => hx (List.mem_of_mem_take h)
  refine WP.mono (hashG_ok (aregs.take k) 0 t₂ (c := (r - 1) % 4 + 1) X' (fun n => if n < r then T₀ n else 0) y
      (by intro h; rw [h] at hlen; simp at hlen; omega_arith) hin (by omega_arith) (by omega_arith)
      (by rw [g₂, a₁]; exact mq) (by rw [g₂, a₁]; exact mb)
      (fun l hl => by rw [keep₂ _ (nA _ (by decide)) (by decide) l hl, h0 l hl])
      (fun l hl => by rw [keep₂ _ (nA _ (by decide)) (by decide) l hl, h2 l hl])
      (by rw [hW₂, e0, hc16, rd₂, wr₂, rd₁, wr₁]; exact hinW)
      (fun n _ => by simp only [Nat.mul_zero, Nat.zero_add]; rfl)
      (fun n _ => by simp only [Nat.mul_zero, Nat.zero_add, hc, hW₂]; rfl)
      (fun h => absurd rfl h)) fun t₃ ⟨p₃, f₃⟩ => ?_
  refine WP.mono (fin_ok t₃ fun l hl => by
      rw [f₃.zlane _ (by decide) l hl, keep₂ _ (nA _ (by decide)) (by decide) l hl, h1 l hl])
    fun t' ⟨y', y1', f'⟩ => ?_
  have acc : ∀ l < 4, prod (t₃.zproj l) = laneAccG (fun n => D n ^^^ K n) T y l r := fun l hl => by
    rw [p₃ l hl, Nat.zero_add, laneAccG_pad X' T₀ y l r (4 * (aregs.take k).length) (by rw [hlen]; omega_arith)]
    exact laneAccG_congr y l r hX' hT₀
  refine ⟨fun n hn => ?_, ?_, ?_, y1', fun q hq => ?_, ?_, ?_, fun x hx hx' l hl => ?_⟩
  · rw [f'.mem, f₃.mem, ← z₂ n hn]; exact hX' n hn
  · rw [f'.mem, f₃.mem, ← m₁]; exact f₂
  · rw [y', acc 0 (by decide), acc 1 (by decide), acc 2 (by decide), acc 3 (by decide)]
  · rw [f'.gpr, f₃.gpr, g₂, g₁ q hq]
  · rw [f'.rd, f₃.rd, rd₂, rd₁]
  · rw [f'.wr, f₃.wr, wr₂, wr₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    obtain ⟨n13, n12, n7, n8, n9, n10, n11, n2⟩ := hx'
    rw [f'.zlane x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨n8, n9, n10, n11, n11, n10, n11, n2⟩) l hl,
      f₃.zlane x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨n12, n7, n8, n9, n10, n11⟩) l hl, keep₂ x (nA x hx) n13 l hl]

/-- The `r` blocks after the last group as a group of `k` registers: their
counters `c …` encrypted, with `g i` after round `i`, the data at `src` added
and the blocks stored to `rdx`, once `pre` (after `rdx` is advanced past the
last group) points them at `S` and `A`, and `Y` their `GHASH` lanes, reduced
and added, from the `Y` that `Q 10` leaves in `xmm2`. -/
theorem ksBatchG_ok {s₀ : State} (hp : SPre s₀) {k r : Nat} (hk4 : k ≤ 4) (hr1 : 1 ≤ r) (hr15 : r ≤ 15)
    (hrk : r ≤ 4 * k) (hkr : 4 * k < r + 4) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    (pre : List Instr) (src : Reg) (hsrc : src ≠ .r10) (hs9 : src ≠ .r9) (hsa : src ≠ .rax)
    {A S W : Addr} {D T : Nat → Block} {y : Block} {c : Nat} {s : State}
    (hpre : ∀ t : State, t.gpr = s.gpr → WP isa (.block (.alu .add .rdx (.imm 256) :: pre)) t fun t' =>
      t'.gpr .rdx = A ∧ t'.gpr src = S ∧ (∀ q, q ≠ .rdx → q ≠ src → t'.gpr q = t.gpr q) ∧
      (∀ x l, t'.zlane x l = t.zlane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr)
    (hQ10 : ∀ t, Q 10 t → (∀ l < 4, t.zlane .xmm1 l = poly) ∧ ∀ l < 4, t.zlane .xmm2 l = if l = 0 then y else 0)
    (hctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask) (hinc : ∀ l < 4, s.zlane .xmm15 l = four)
    (hrdi : s.gpr .rdi = kp s₀) (hrsi : s.gpr .rsi = s₀.gpr .rsi)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hfr : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s.mem)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hgh : ∀ j, (g j).all Instr.keepsH = true) (hQ : Q 1 s)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) (hW : s.gpr .rax = W)
    (hD : ∀ n < r, blockAt s.mem (S + BitVec.ofNat 64 (16 * n)) = D n)
    (hT : ∀ n < r, s.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128 = T n)
    (hinS : InRegions (s.rd ++ s.wr) S (16 * r)) (hinD : InRegions s.wr A (16 * r))
    (hinW : InRegions (s.rd ++ s.wr) W (16 * r))
    (hsep : ∀ n q', q' < n / 4 → n < r →
      Region.Disjoint ⟨S + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A + BitVec.ofNat 64 (64 * q'), 64⟩)
    (hWA : ∀ n < r, Region.Disjoint ⟨W + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A, 16 * r⟩) :
    WP isa (Impl.Gcm.X86_64.StitchZH.ksBatchG k g pre src) s fun s' =>
      (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
        D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
      Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
      s'.zlane .xmm2 0 =
        (reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 0 r) ^^^
          reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 2 r)) ^^^
        (reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 1 r) ^^^
          reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 3 r)) ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      (∀ q, q ≠ .r10 → q ≠ .rdx → q ≠ src → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) →
        x ≠ .xmm14 → x ∉ G → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
  have hK : Keys (nr s₀) (sch s₀) s := keys_of hp hrdi hrd hwr hfr
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hnd' : (aregs.take k).Nodup := hnd.sublist (List.take_sublist _ _)
  have hx' : ∀ r ∈ aregs.take k, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := fun r hr => hx r (List.mem_of_mem_take hr)
  have h13' : .xmm13 ∉ aregs.take k := fun h => h13 (List.mem_of_mem_take h)
  have hlen : (aregs.take k).length = k := by simp [aregs]; omega_arith
  refine WP.seq (WP.mono (WP.hkeep (ctrsZ_keeps _ _ _ _) (ctrsZ_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide)
    (aregs.take k) s (cb s₀) c hnd' hx' hctr hmsk hinc)) fun s₁ ⟨⟨e₁, c₁, f₁⟩, hh₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys hK f₁
  have hCache₁ := hCache.keep hh₁ hK₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hr)))
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZH.aes_ok .xmm13 (aregs.take k) hnd' h13' hp.rounds g G
    (fun r h hm => (hG r h).1 (List.mem_of_mem_take hm)) Q
    (fun j hj h9 t hk hq => WP.mono (WP.hkeep (hgh j) (hg j hj h9 t hk.base hq))
      fun _ ⟨⟨hq', hf⟩, hh⟩ => ⟨hq', hf, hh⟩)
    (fun j s s' h f => hq j s s' h (f.toZFrame.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hr)))) s₁ hCache₁ hQ₁
    (by rw [f₁.gpr, hrsi]; simp)) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ n < r, XBinOp.eval .pshufb (s₂.zlane ((aregs.take k).getD (n / 4) .xmm0) (n % 4)) revMask =
      ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀)) := fun n hn => by
    have h : n / 4 < (aregs.take k).length := by rw [hlen]; omega_arith
    rw [← List.getElem_eq_getD (h := h),
      (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) _ (by omega_arith), e₁ _ h _ (by omega_arith)])).symm,
      show c + 4 * (n / 4) + n % 4 = c + n by omega_arith]
  have hg₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  have hrd₂ : s₂.rd = s.rd := by rw [f₂.rd, f₁.rd]
  have hwr₂ : s₂.wr = s.wr := by rw [f₂.wr, f₁.wr]
  have keep₂ : ∀ x, x ∉ aregs → x ≠ .xmm13 → x ≠ .xmm14 → x ∉ G → ∀ l < 4, s₂.zlane x l = s.zlane x l :=
    fun x hx h13 h14 hg l hl => by
      rw [f₂.zlane x (by
        simp only [List.mem_cons, List.mem_append, not_or]
        exact ⟨h13, fun h => hx (List.mem_of_mem_take h), hg⟩) l hl,
        f₁.zlane x (by
          simp only [List.mem_cons, not_or]
          exact ⟨h14, fun h => hx (List.mem_of_mem_take h)⟩) l hl]
  obtain ⟨q1, q2⟩ := hQ10 s₂ hQ₂
  refine WP.seq (WP.mono (hpre s₂ hg₂) fun s₃ ⟨d₃, src₃, g₃, l₃, m₃, rd₃, wr₃⟩ => ?_)
  have gk₃ : ∀ q, q ≠ .rdx → q ≠ src → s₃.gpr q = s.gpr q := fun q h1 h2 => by rw [g₃ q h1 h2, hg₂]
  refine WP.mono (tailG_ok src hsrc hk4 hr1 hr15 hrk hkr (t := s₃)
      (K := fun n => ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) (D := D) (T := T) (y := y)
      (by rw [gk₃ _ (by decide) (Ne.symm hs9), h9]) d₃ src₃ (by rw [gk₃ _ (by decide) (Ne.symm hsa), hW])
      (fun n hn => by rw [l₃]; exact ks n hn)
      (fun n hn => by rw [m₃, hm₂]; exact hD n hn) (fun n hn => by rw [m₃, hm₂]; exact hT n hn)
      (by rw [rd₃, wr₃, hrd₂, hwr₂]; exact hinS) (by rw [wr₃, hwr₂]; exact hinD)
      (by rw [rd₃, wr₃, hrd₂, hwr₂]; exact hinW) hsep hWA
      (fun l hl => by rw [l₃, keep₂ _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.1 rfl) l hl]
                      exact hmsk l hl)
      (fun l hl => by rw [l₃]; exact q1 l hl) (fun l hl => by rw [l₃]; exact q2 l hl))
    fun s' ⟨b', f', y', y1', g', rd', wr', z'⟩ => ⟨b', by rw [← hm₂, ← m₃]; exact f', y', y1',
      fun q h1 h2 h3 => by rw [g' q h1, gk₃ q h2 h3], by rw [rd', rd₃, hrd₂], by rw [wr', wr₃, hwr₂],
      fun x hx hx' h14 hg l hl => by
        rw [z' x hx hx' l hl, l₃, keep₂ x hx (fun h => hx' (h ▸ List.mem_cons_self)) h14 hg l hl]⟩

end VG.Proof.Gcm.X86_64.StitchZH
