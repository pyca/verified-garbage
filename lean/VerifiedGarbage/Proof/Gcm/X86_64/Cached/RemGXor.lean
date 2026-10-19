module
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemQuadK
import VerifiedGarbage.Proof.Framework.X86_64.MaskedPrefix
import VerifiedGarbage.Proof.Framework.X86_64.ZFrameBlock
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.Gcm.Precomputed

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
      simp only [s₂, zlane_zbin _ _ _ _ _ _ (show l < 4 by omega), ite_true, ZBinOp.sse]
      rw [zlane_setZv _ _ _ (by omega), lv l (by omega), ite_eq_left hl, State.zlane_setZ_ne _ hb _ _ _ _ (by omega)]
      simp only [VG.Proof.Aes.X86_64.AesNi.eval_pxor]
  have bD : ∀ l < c, blockAt m₃ (a + BitVec.ofNat 64 (16 * l)) =
      XBinOp.eval .pshufb (s₂.zlane b l) revMask := fun l hl => by
    rw [blockAt_eq]
    have e := readW_writeW_inside s.mem a ((s₂.zmm b).setWidth (128 * c)) (k := 16 * l) (n := 16)
      (by omega) (by omega)
    rw [show 8 * 16 = 128 by rfl] at e
    rw [e, show 8 * (16 * l) = 128 * l by omega]
    have e2 : ((s₂.zmm b).setWidth (128 * c)).extractLsb' (128 * l) 128 = (s₂.zmm b).extractLsb' (128 * l) 128 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
      rw [decide_eq_true (show 128 * l + i < 128 * c by omega), Bool.true_and]
    rw [e2, zmm_lane _ _ (by omega)]
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
      rw [Offset.add_add, Offset.add_add, show 64 * j + 16 * n = 16 * (4 * j + n) by omega] at this
      rw [this, show n / 4 = 0 by omega, show n % 4 = n by omega]; rfl
    · have := z' n hn
      rw [Offset.add_add, show 64 * j + 16 * n = 16 * (4 * j + n) by omega] at this
      rw [← this, show n / 4 = 0 by omega, show n % 4 = n by omega]; rfl
    · rw [m']
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (by rw [show 128 * c / 8 = 16 * c by omega]; exact Region.contains_self _ _)
  | b :: b₂ :: bs, j, s, c, _, hnd, h13, hc, hk, hb, hinS, hinD, hsep, hw => by
    have hb13 : b ≠ .xmm13 := fun h => h13 (h ▸ List.mem_cons_self)
    have hbs : b ∉ b₂ :: bs := (List.nodup_cons.mp hnd).1
    have h13' : .xmm13 ∉ b₂ :: bs := fun h => h13 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hinS hinD hsep hw ⊢
    rw [show xorG src (b :: b₂ :: bs) j = ([.vmovdqu32Load .xmm13 (at_ src (64 * j)), .zop (.zbin .vpxord b b .xmm13),
      .vmovdqu32Store (at_ .rdx (64 * j)) b] : List Instr) ++ xorG src (b₂ :: bs) (j + 1) from rfl,
      WP.block_append_iff]
    have hlen : 64 ≤ 64 * (bs.length + 1 + 1 - 1) + 16 * c := by omega
    have hn64 : 64 * (bs.length + 1 + 1 - 1) + 16 * c < 2 ^ 64 := by omega
    refine WP.mono (xor1G_ok src b (64 * j) s hb13
      (by have := CallLay.inRegions_sub (off := 0) (l := 64) hinS (by omega) hn64
          rwa [show s.gpr src + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 0 = s.gpr src + BitVec.ofNat 64 (64 * j)
            from BitVec.add_zero _] at this)
      (by have := CallLay.inRegions_sub (off := 0) (l := 64) hinD (by omega) hn64
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
          (by simp only [List.length_cons]; omega) hn64
        rwa [Offset.add_add, show 64 * j + 64 = 64 * (j + 1) by omega] at this)
      (by
        rw [wr₁, g₁]
        have := CallLay.inRegions_sub (off := 64) (l := 64 * ((b₂ :: bs).length - 1) + 16 * c) hinD
          (by simp only [List.length_cons]; omega) hn64
        rwa [Offset.add_add, show 64 * j + 64 = 64 * (j + 1) by omega] at this)
      (fun n q' hq hn => by
        rw [g₁, show 4 * (j + 1) + n = 4 * j + (n + 4) by omega, show j + 1 + q' = j + (q' + 1) by omega]
        exact hsep (n + 4) (q' + 1) (by omega) (by simp only [List.length_cons] at hn ⊢; omega))
      (by simp only [List.length_cons] at hw ⊢; omega))
      fun s' ⟨b', z', f', g', rd', wr', k'⟩ => ?_
    simp only [List.length_cons] at b' z' f'
    rw [g₁] at b' z' f'
    -- The first register's blocks, which the later writes keep.
    have keep0 : ∀ n < 4, blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (4 * j + n))) =
        blockAt s₁.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (4 * j + n))) := fun n hn =>
      blockAt_frame f' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    -- The later registers' data, which the first write keeps.
    have keepS : ∀ n, 4 ≤ n → n < 4 * (bs.length + 1) + c →
        blockAt s₁.mem (s.gpr src + BitVec.ofNat 64 (16 * (4 * j + n))) =
          blockAt s.mem (s.gpr src + BitVec.ofNat 64 (16 * (4 * j + n))) := fun n h4 hn => by
      rw [m₁]
      apply Stitch.blockAt_writeW_sep' (R := ⟨s.gpr .rdx + BitVec.ofNat 64 (64 * j), 64⟩) _ rfl
      have := hsep n 0 (by omega) (by omega)
      rwa [Nat.add_zero] at this
    refine ⟨fun n hn => ?_, fun n hn => ?_, ?_, by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁],
      fun r hr h13'' l hl => ?_⟩
    · by_cases h4 : n < 4
      · rw [keep0 n h4]
        have := b₁ n h4
        rw [Offset.add_add, Offset.add_add, show 64 * j + 16 * n = 16 * (4 * j + n) by omega] at this
        rw [this, show n / 4 = 0 by omega, show n % 4 = n by omega]; rfl
      · have := b' (n - 4) (by omega)
        rw [show 4 * (j + 1) + (n - 4) = 4 * j + n by omega, show (n - 4) / 4 = n / 4 - 1 by omega,
          show (n - 4) % 4 = n % 4 by omega] at this
        rw [this, keepS n (by omega) (by omega)]
        have hq : n / 4 = (n / 4 - 1) + 1 := by omega
        rw [hq, List.getD_cons_succ, Nat.add_sub_cancel, k₁ _ (fun h => by
          have hm : (b₂ :: bs).getD (n / 4 - 1) .xmm0 ∈ b₂ :: bs := by
            rw [← List.getElem_eq_getD (h := by simp only [List.length_cons]; omega)]
            exact List.getElem_mem _
          exact hbs (h ▸ hm)) (fun h => by
          have hm : (b₂ :: bs).getD (n / 4 - 1) .xmm0 ∈ b₂ :: bs := by
            rw [← List.getElem_eq_getD (h := by simp only [List.length_cons]; omega)]
            exact List.getElem_mem _
          exact h13' (h ▸ hm)) _ (by omega)]
    · by_cases h4 : n < 4
      · rw [keep0 n h4, show n / 4 = 0 by omega, show n % 4 = n by omega, List.getD_cons_zero,
          k' b hbs hb13 _ (by omega)]
        have := z₁ n h4
        rw [Offset.add_add, show 64 * j + 16 * n = 16 * (4 * j + n) by omega] at this
        exact this
      · have := z' (n - 4) (by omega)
        rw [show 4 * (j + 1) + (n - 4) = 4 * j + n by omega, show (n - 4) / 4 = n / 4 - 1 by omega,
          show (n - 4) % 4 = n % 4 by omega] at this
        rw [show n / 4 = (n / 4 - 1) + 1 by omega, List.getD_cons_succ]
        exact this
    · have F1 : Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (64 * j), 64 * (bs.length + 1 + 1 - 1) + 16 * c⟩]
          s.mem s₁.mem := by
        rw [m₁]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
      exact F1.trans (f'.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩)
    · rw [k' r (fun h => hr (List.mem_cons_of_mem _ h)) h13'' l hl,
        k₁ r (fun h => hr (h ▸ List.mem_cons_self)) h13'' l hl]

end VG.Proof.Gcm.X86_64.StitchZH
