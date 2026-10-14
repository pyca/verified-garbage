module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopD
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP

/-!
# The blocks after the last group, decrypted

`remD_ok`: once the decryption loop stops with `r = nb mod 16` blocks left
(`DInv`, the groups already hashed and decrypted), `StitchZH.remD` stores the
counter after all the blocks (`remSetup_ok`), computes the keystream of the
`r` blocks (`ksSelWith_ok`, with nothing between the rounds), hashes and
decrypts the `r` blocks (`remLoopsD_ok`), and stores `Y`. `decTailRG_ok`
is `dec` after its setup for any number of blocks from 16 on.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre DPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀
  addr_eq in_sub in_sub_int in_rdwr blocks_ctr32 blockAt_writeW_sep' ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB toNat_ofNat_lt)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZH (ksSelWith remD remSetup remLoopsD dbody)
open VG.Proof.Gcm.X86_64.StitchZ (DInv AInv FinOk Ready cmp_ok dfinal_ok)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- `add r9, 16`. -/
theorem add9_ok (s : State) :
    WP isa (.block [.alu .add .r9 (.imm 16)]) s fun s' =>
      s'.gpr .r9 = s.gpr .r9 + 16 ∧ (∀ q, q ≠ .r9 → s'.gpr q = s.gpr q) ∧ (∀ x l, s'.zlane x l = s.zlane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    State.setReg, e16, ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `test r9, r9`. -/
theorem test99_ok (s : State) :
    WP isa (.block [.alu .test .r9 (.reg .r9)]) s fun s' =>
      s'.zf = some (s.gpr .r9 &&& s.gpr .r9 == 0) ∧ s'.gpr = s.gpr ∧ (∀ x l, s'.zlane x l = s.zlane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- Before the loops: `r10 = 0`, and the products cleared. -/
theorem remPreD_ok (s : State) :
    WP isa (.block (([.mov32 .r10 (.imm 0)] : List Instr) ++ Impl.Gcm.X86_64.StitchAvx.zero)) s
      fun s' => s'.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧ (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧
        (∀ l < 4, s'.zlane .xmm8 l = 0 ∧ s'.zlane .xmm9 l = 0 ∧ s'.zlane .xmm10 l = 0) ∧
        (∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [WP.block_append_iff]
  have hA : WP isa (.block [.mov32 .r10 (.imm 0)]) s fun s₁ =>
      s₁.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧ (∀ q, q ≠ .r10 → s₁.gpr q = s.gpr q) ∧
      (∀ x l, s₁.zlane x l = s.zlane x l) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, isa, State.setReg,
      ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨rfl, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩
  refine WP.mono hA fun s₁ ⟨z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (zeroZ_ok s₁) fun s' ⟨zz, f', g', m', rd', wr'⟩ =>
    ⟨by rw [g', z₁], fun q h => by rw [g', g₁ q h], zz,
      fun x h8 h9 h10 l hl => by rw [f' x h8 h9 h10 l hl, l₁], by rw [m', m₁], by rw [rd', rd₁], by rw [wr', wr₁]⟩

theorem remD_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hr : RemOk (hk s₀) P) {e : Nat}
    {s : State} (hI : DInv s₀ P e s) (hlt : nb s₀ - 16 * e < 16) (hne : nb s₀ ≠ 16 * e)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq (.block [.alu .add .r9 (.imm 16)]) remD) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have hle := hI.a.le
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by omega
  have hr15 : r ≤ 15 := by omega
  refine WP.seq (WP.mono (WP.hkeep (by decide) (add9_ok s)) fun s' ⟨⟨a9, ga, la, ma, rda, wra⟩, hha⟩ => ?_)
  have hr9 : s'.gpr .r9 = BitVec.ofNat 64 (16 + r) := by
    rw [a9, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
    congr 1; omega
  have hrax : s'.gpr .rax = cp s₀ := by rw [ga _ (by decide)]; exact hI.rax
  have hr11 : s'.gpr .r11 = pp s₀ := by
    rw [ga _ (by decide)]; exact hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  have hA' : AInv s₀ (16 * e) s' :=
    ⟨hI.a.le, fun l hl => by rw [la]; exact hI.a.ctr l hl, fun l hl => by rw [la]; exact hI.a.msk l hl,
      fun l hl => by rw [la]; exact hI.a.inc l hl, by rw [ga _ (by decide)]; exact hI.a.rdi,
      by rw [ga _ (by decide)]; exact hI.a.rsi, by rw [ga _ (by decide)]; exact hI.a.r10,
      by rw [ma]; exact hI.a.frame, fun k hk => by rw [ma]; exact hI.a.blocks k hk, by rw [rda]; exact hI.a.rd,
      by rw [wra]; exact hI.a.wr⟩
  have hCache' := hCache.keep hha (hA'.keys hp)
  rw [show remD = .seq (.block remSetup) (.seq (ksSelWith fun _ => [])
      (.seq (.block (([.mov32 .r10 (.imm 0)] : List Instr) ++ Impl.Gcm.X86_64.StitchAvx.zero))
        (.seq (remLoopsD .rdx) (.block storeY)))) from rfl]
  -- The counter after all the blocks, and the powers of the `r` blocks.
  refine WP.seq (WP.mono (WP.hkeep (by decide) (remSetup_ok s' hr1 hr15 hr9
    (by rw [← State.zlane_lt2 _ _ (by decide), la]; exact hI.a.msk 0 (by decide))
    (by rw [hrax, wra, hI.a.wr]; exact in_sub_int hp.c_in (by omega))))
    fun s₁ ⟨⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  have e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hrax, e0, ma] at m₁
  rw [hr11] at ax₁
  have gk₁ : ∀ q, q ≠ .r10 → q ≠ .rax → q ≠ .r9 → s₁.gpr q = s.gpr q := fun q h1 h2 h3 => by
    rw [g₁ q h1 h2, ga q h3]
  have zk₁ : ∀ x, x ≠ .xmm13 → ∀ l < 4, s₁.zlane x l = s.zlane x l := fun x h l hl => by rw [z₁ x h l hl, la]
  have cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  have hfr₁ : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cw
  have hrd₁ : s₁.rd = s₀.rd := by rw [rd₁, rda]; exact hI.a.rd
  have hwr₁ : s₁.wr = s₀.wr := by rw [wr₁, wra]; exact hI.a.wr
  have hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [gk₁ _ (by decide) (by decide) (by decide)]; exact hI.a.rdi
  have hCache₁ := hCache'.keep hh₁ (keys_of hp hrdi₁ hrd₁ hwr₁ hfr₁)
  -- The keystream.
  refine WP.seq (WP.mono (ksSelWith_ok hp hr1 hr15 (fun _ => []) [] (fun _ h => absurd h List.not_mem_nil)
    (fun _ => rfl) (fun _ _ => True) (fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
    (c := 16 * e) a10₁ (fun l hl => by rw [zk₁ _ (by decide) l hl]; exact hI.a.ctr l hl)
    (fun l hl => by rw [zk₁ _ (by decide) l hl]; exact hI.a.msk l hl)
    (fun l hl => by rw [zk₁ _ (by decide) l hl]; exact hI.a.inc l hl) hrdi₁
    (by rw [gk₁ _ (by decide) (by decide) (by decide)]; exact hI.a.rsi)
    (by rw [g₁ _ (by decide) (by decide)]; exact hr11) hrd₁ hwr₁ hfr₁ hCache₁ trivial)
    fun s₂ ⟨_, ks₂, g₂, rd₂, wr₂, l₂, f₂⟩ => ?_)
  -- `r10 = 0`, the products cleared.
  refine WP.seq (WP.mono (remPreD_ok s₂) fun s₃ ⟨z₃, g₃, p₃, l₃, m₃, rd₃, wr₃⟩ => ?_)
  have gk₃ : ∀ q, q ≠ .r10 → q ≠ .rax → q ≠ .r9 → s₃.gpr q = s.gpr q := fun q h1 h2 h3 => by
    rw [g₃ q h1, g₂, gk₁ q h1 h2 h3]
  have zk₃ : ∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs →
      ∀ l < 4, s₃.zlane x l = s.zlane x l := fun x h8 h9 h10 h13 h14 ha l hl => by
    rw [l₃ x h8 h9 h10 l hl, l₂ x h13 h14 ha List.not_mem_nil l hl, zk₁ x h13 l hl]
  have hA : s₃.gpr .rdx = bAddr s₀ (16 * e) := by
    rw [gk₃ _ (by decide) (by decide) (by decide), hI.rdx]
    show dp s₀ + BitVec.ofNat 64 (256 * e) = dp s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [show 256 * e = 16 * (16 * e) by omega]
  let E : REnv := REnv.mk r .rdx (bAddr s₀ (16 * e)) (bAddr s₀ (16 * e)) (pp s₀)
    (pp s₀ + BitVec.ofNat 64 (256 - 16 * r)) s₃.mem s₃.gpr s₃.rd s₃.wr (s₃.lane .xmm2 0)
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hrd₁]
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hwr₁]
  have hE : E.Ok :=
    { r1 := hr1, r15 := hr15, gS := hA, gA := hA,
      gP := by show s₃.gpr .r11 = _; rw [g₃ _ (by decide), g₂, g₁ _ (by decide) (by decide), hr11]
      gW := by show s₃.gpr .rax = _; rw [g₃ _ (by decide), g₂, ax₁]
      src9 := by show Reg.rdx ≠ Reg.r9; decide, src10 := by show Reg.rdx ≠ Reg.r10; decide
      inS := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inK := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [hrd₃, hwr₃]
        exact in_rdwr (in_sub hp.p_in (by omega))
      inD := fun j (hj : j < r) => by
        show InRegions s₃.wr (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.d_in (by omega)
      inW := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega))
      dS := fun j (hj : j < r) i hi => by
        show Region.Disjoint ⟨bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ (16 * e), 16 * i⟩
        exact Offset.disjoint_base _ (by omega) (by omega)
      dK := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (768 + 16 * j), 16⟩ ⟨bAddr s₀ (16 * e), 16 * r⟩
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
      dW := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨bAddr s₀ (16 * e), 16 * r⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)) }
  have h4 : E.Ok4 :=
    { inS4 := fun j (hj : j + 4 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 64
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inK4 := fun j (hj : j + 4 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (768 + 16 * j)) 64
        rw [hrd₃, hwr₃]
        exact in_rdwr (in_sub hp.p_in (by omega))
      inD4 := fun j (hj : j + 4 ≤ r) => by
        show InRegions s₃.wr (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 64
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.d_in (by omega)
      inW4 := fun j (hj : j + 4 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 64
        rw [hrd₃, hwr₃, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega))
      dW4 := fun j (hj : j + 4 ≤ r) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j), 64⟩
          ⟨bAddr s₀ (16 * e), 16 * r⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)) }
  have hI₃ : RInv1D E 0 s₃ :=
    { le := Nat.zero_le _, r10 := z₃
      r9 := by
        show s₃.gpr .r9 = _
        rw [g₃ _ (by decide), g₂, g₁ _ (by decide) (by decide), hr9, Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := by
        obtain ⟨a, b, c⟩ := p₃ 0 (by decide)
        simp only [prod, State.proj_xmm, ← State.zlane_lt2 _ _ (show 0 < 2 by decide), a, b, c]
        rfl
      zhi := fun l _ hl => p₃ l hl
      y := fun l hl => by
        rcases Nat.eq_zero_or_pos l with rfl | hl0
        · rw [State.zlane_lt2 _ _ (by decide)]; rfl
        · rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)),
            zk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl]
          exact hI.y1 l hl0 hl
      m0 := fun l hl => by
        rw [zk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl]
        exact hI.a.msk l hl
      m1 := fun l hl => by
        rw [zk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl]
        exact hI.m1 l hl }
  refine WP.seq (WP.mono (remLoopsD_ok hE h4 hI₃) fun s₄ hI₄ => ?_)
  -- `Y` stored.
  have hrcx : s₄.gpr .rcx = yp s₀ := by
    rw [hI₄.gpr _ (by decide) (by decide)]
    show s₃.gpr .rcx = _
    rw [gk₃ _ (by decide) (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (Gcm.X86_64.StitchZ.store16Z_ok .xmm2 .xmm2 .rcx s₄ hI₄.m0
    (by rw [hrcx, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.y_in))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx] at m₆
  have hnb : nb s₀ = 16 * e + r := by omega
  -- What the stages keep of the memory before them.
  have toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) → Region.Disjoint ⟨p, 16⟩ (ksR s₀) →
      blockAt s₃.mem p = blockAt s.mem p := fun p hc hk => by
    rw [m₃, blockAt_frame f₂ (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hk), m₁,
      show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  have ksP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (ksR s₀) := fun k hk =>
    (hp.d_p.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  have cP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have hS : ∀ j < r, blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) = blk s₀ (16 * e + j) :=
    fun j hj => by
      have hk : 16 * e + j < nb s₀ := by omega
      rw [Offset.add_add, ← Nat.mul_add, toS _ (cP _ hk) (ksP _ hk), hI.a.blocks _ hk]
      simp only [show ¬ 16 * e + j < 16 * e by omega, ite_false]
  -- The blocks.
  have hb₄ : ∀ k < nb s₀, blockAt s₄.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame hI₄.frame (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          show Region.Disjoint _ ⟨bAddr s₀ (16 * e), 16 * r⟩
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)),
        toS _ (cP k hk) (ksP k hk), hI.a.blocks k hk]
      simp only [hke, ite_true]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega⟩
      have hj : j < r := by omega
      have ct := hI₄.ct j hj
      have eD : E.aD j = bAddr s₀ (16 * e + j) := by
        show bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j) = _
        rw [Offset.add_add, ← Nat.mul_add]
      rw [eD] at ct
      rw [ct]
      show blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) ^^^
        blockAt s₃.mem (pp s₀ + BitVec.ofNat 64 (768 + 16 * j)) = _
      rw [hS j hj, m₃, ks₂ j hj]
  have hH : ∀ j < r, E.H j = blk s₀ (16 * e + j) := fun j hj => hS j hj
  have hT : ∀ j < r, E.T j = P ((16 - r + j) / 4) ((16 - r + j) % 4) := fun j hj => by
    show s₃.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 128 = _
    have hm : 16 - r + j < 16 := by omega
    rw [Offset.add_add, show 256 - 16 * r + 16 * j = 64 * ((16 - r + j) / 4) + 16 * ((16 - r + j) % 4) by omega,
      m₃, f₂.readW (r := ⟨pp s₀ + BitVec.ofNat 64 (64 * ((16 - r + j) / 4) + 16 * ((16 - r + j) % 4)), 16⟩)
        (Region.contains_self _ _) (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide),
      m₁, Mem.readW_writeW_sep ((hp.p_c.sub_left (Offset.sub_base _ (by omega))).sep
          (Region.contains_self _ _) cw) (by decide)]
    exact hI.pw _ (by omega) _ (by omega)
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < nb s₀, blockAt s₆.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yD k hk) rfl, hb₄ k hk]
  have fA : ∀ R : Region, R.Disjoint (dR s₀) → ∀ r' ∈ [(⟨E.A, 16 * E.r⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega))
  have hy₃ : s₃.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀)) := by
    rw [← State.zlane_lt2 _ _ (show 0 < 2 by decide),
      zk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
    exact hI.y
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show blockAt s₆.mem (cp s₀) = _
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl,
      blockAt_frame hI₄.frame (fA _ hp.d_c.symm), show E.m = s₃.mem from rfl, m₃,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.p_c.symm.sub_right (Offset.sub_base _ (by omega))),
      m₁, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), la, hI.a.ctr 0 (by decide),
      Nat.add_zero, VG.Proof.Aes.X86_64.AesNi.rep_add, hnb]
  · show blockAt s₆.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
    have hbl : blocksAt s₀.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (blk s₀) := rfl
    rw [hbl, m₆, VG.Proof.Gcm.X86_64.blockAt_store, hI₄.y, laneAcc_congr _ _ 0 r hH hT,
      laneAcc_congr _ _ 1 r hH hT, laneAcc_congr _ _ 2 r hH hT, laneAcc_congr _ _ 3 r hH hT, hr r hr1 hr15,
      show E.y = s₃.lane .xmm2 0 from rfl, hy₃, hnb, List.range_add, List.map_append, List.map_map]
    simp only [ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₆.mem
    have F0 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem := hI.a.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    have F1 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    have F2 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₁.mem s₃.mem := by
      rw [m₃]
      exact f₂.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega)⟩
    have F3 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₃.mem s₄.mem := hI₄.frame.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨dR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega)⟩
    rw [m₆]
    exact (((F0.trans F1).trans F2).trans F3).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4
    show s₆.gpr q = _
    rw [g₆, hI₄.gpr q h3 h4]
    show s₃.gpr q = _
    rw [gk₃ q h4 h1 h3]
    exact hI.gpr q h1 h2 h3 h4
  · show s₆.rd = _
    rw [rd₆, hI₄.rd]; exact hrd₃
  · show s₆.wr = _
    rw [wr₆, hI₄.wr]; exact hwr₃

/-- The decryption loop, for any number of blocks: it stops with fewer than 16 left. -/
theorem loopDR_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    {s : State} (hI : DInv s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * e < 16)))
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.ite .b (.block []) (.loop dbody .ae)) s fun s' => ∃ e, nb s₀ - 16 * e < 16 ∧ DInv s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have hle := hI.a.le
  refine WP.ite (decide (nb s₀ - 16 * e < 16)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨e, by simpa using h, hI, hCache⟩
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ DInv s₀ P e s ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s
    have hstep : ∀ m s, I m s → WP isa dbody s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * e < 16 ∧ DInv s₀ P e s' ∧
          VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI, hCI⟩
      refine WP.mono (dbody_ok hp hf he hI hCI) fun s' ⟨hI', hcf', hCI'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * (e + 1) < 16
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          e + 1, hlt, hI', hCI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by omega, e + 1, rfl, by omega, hI', hCI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * e) s ⟨e, rfl, by simp at h; omega, hI, hCache⟩

/-- `decR` after the setup, for any number of blocks from 16 on. -/
theorem decTailRG_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOk (hk s₀) P)
    {bigC : Prog isa} (hbig : ∀ s, 256 ≤ nb s₀ → DInv s₀ P 0 s → VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s →
      WP isa bigC s fun s' => ∃ e, DInv s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s')
    {s : State} (hR : Ready s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq (.block [.alu .cmp .r9 (.imm 256)]) (.seq (.ite .b (.block []) bigC)
      (.seq (.block [.alu .cmp .r9 (.imm 16)])
        (.seq (.ite .b (.block []) (.loop dbody .ae))
          (.seq (.block [.alu .test .r9 (.reg .r9)])
            (.ite .e (.block (storeCtr ++ storeY)) (.seq (.block [.alu .add .r9 (.imm 16)]) remD))))))) s
      (DPost s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hI₁ : DInv s₀ P 0 s :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp_ok s 256 256 (by decide)))
    fun s₂ ⟨⟨hcf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₂ := hI₁.of_eq g l m rd wr
  have hCache₂ := hCache.keep hh (hI₂.a.keys hp)
  rw [hI₁.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, DInv s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * 0 < 256))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨0, hI₂, hCache₂⟩)
    (fun h => hbig _ (by simp at h; omega) hI₂ hCache₂)) fun s₃ ⟨e, hI₃, hCache₃⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp_ok s₃ 16 16 (by decide)))
    fun s₄ ⟨⟨hcf₄, g₄, l₄, m₄, rd₄, wr₄⟩, hh₄⟩ => ?_)
  have hI₄ := hI₃.of_eq g₄ l₄ m₄ rd₄ wr₄
  have hle := hI₃.a.le
  rw [hI₃.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)] at hcf₄
  refine WP.seq (WP.mono (loopDR_ok hp hf hI₄ hcf₄ (hCache₃.keep hh₄ (hI₄.a.keys hp))) fun s₅ ⟨e, hlt, hI₅, hC₅⟩ => ?_)
  have hle₅ := hI₅.a.le
  refine WP.seq (WP.mono (WP.hkeep (by decide) (test99_ok s₅)) fun s₆ ⟨⟨z₆, g₆, l₆, m₆, rd₆, wr₆⟩, hh₆⟩ => ?_)
  have hI₆ := hI₅.of_eq g₆ (fun x l => l₆ x l) m₆ rd₆ wr₆
  have hz : (s₅.gpr .r9 &&& s₅.gpr .r9 == 0) = decide (nb s₀ = 16 * e) := by
    rw [BitVec.and_self, hI₅.r9]
    by_cases h : nb s₀ = 16 * e
    · rw [show nb s₀ - 16 * e = 0 by omega, decide_eq_true h]; rfl
    · have : BitVec.ofNat 64 (nb s₀ - 16 * e) ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega
      rw [beq_false_of_ne this, decide_eq_false h]
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, z₆, hz]) (fun h => ?_) (fun h => ?_)
  · exact dfinal_ok hp (by simpa using h) hI₆
  · exact remD_ok hp hr hI₆ hlt (by simpa using h) (hC₅.keep hh₆ (hI₆.a.keys hp))

end VG.Proof.Gcm.X86_64.StitchZH
