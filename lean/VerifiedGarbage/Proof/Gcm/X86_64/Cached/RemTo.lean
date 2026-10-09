import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48To

/-!
# The blocks after the last group, out of place

`remTo_ok`: `StitchZHTo.remTo` is `StitchZH.rem` reading the `r` blocks
after the last group from the plaintext (at `rdx + r8`, `r8` holding
`src - dst`) and writing them to the output: the counter after all the
blocks (`remSetup_ok`), the keystream of the `r` blocks while the last group
of the output is hashed (`ksSel_ok`, on the in-place view `dst s₀`), the
`r` blocks encrypted and their products with their powers added
(`remLoop_ok`), and reduced into `Y`.
-/

namespace VG.Proof.Gcm.X86_64.StitchZHTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR addr_eq in_sub in_sub_int in_rdwr blockAt_writeW_sep' ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (gq lastG)
open VG.Impl.Gcm.X86_64.StitchZH (ksSel remWith remSetup remBody remNext tailR)
open VG.Impl.Gcm.X86_64.StitchZHTo (remTo)
open VG.Proof.Gcm.X86_64.StitchZ (GEnv QG gq_ok FinOk)
open VG.Proof.Gcm.X86_64.StitchZTo (EInvTo dst dst_gpr_ne dst_mem sAddr oAddr ctbT blocks_ctr32To finalTo_ok)
open VG.Proof.Gcm.X86_64.StitchZH (RemOk REnv RInv ksR ksSel_ok QG.ksR remSetup_ok remLoop_ok keys_of cmp16_ok
  accR_congr)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- Before the loop: `rdx` at the output blocks, `r8` at the plaintext
blocks, `r10 = 0`, and the products cleared. -/
theorem remPreTo_ok (s : State) :
    WP isa (.block (([.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)] : List Instr) ++
      ([.alu .add .r8 (.reg .rdx)] : List Instr) ++ Impl.Gcm.X86_64.StitchAvx.zero)) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r8 = s.gpr .r8 + (s.gpr .rdx + 256) ∧
        s'.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
        (∀ q, q ≠ .rdx → q ≠ .r10 → q ≠ .r8 → s'.gpr q = s.gpr q) ∧ prod (s'.proj 0) = Prod.zero ∧
        (∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → s'.lane x 0 = s.lane x 0) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  rw [WP.block_append_iff]
  have hA : WP isa (.block ([.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)] ++
      ([.alu .add .r8 (.reg .rdx)] : List Instr))) s fun s₁ =>
      s₁.gpr .rdx = s.gpr .rdx + 256 ∧ s₁.gpr .r8 = s.gpr .r8 + (s.gpr .rdx + 256) ∧
      s₁.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
      (∀ q, q ≠ .rdx → q ≠ .r10 → q ≠ .r8 → s₁.gpr q = s.gpr q) ∧ (∀ x l, s₁.lane x l = s.lane x l) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, readSrc32, arithFlags, State.setFlags, State.setReg32, isa, State.setReg, e256, reduceCtorEq,
      ↓reduceIte, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, rfl, fun q h1 h2 h3 => by simp only [h1, h2, h3, ↓reduceIte], fun _ _ => rfl, trivial,
      trivial, trivial⟩
  refine WP.mono hA fun s₁ ⟨d₁, r₁, z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (Gcm.X86_64.StitchAvx.zero_ok s₁) fun s' ⟨p', f'⟩ =>
    ⟨by rw [f'.gpr, d₁], by rw [f'.gpr, r₁], by rw [f'.gpr, z₁], fun q h1 h2 h3 => by rw [f'.gpr, g₁ q h1 h2 h3],
      p', fun x h8 h9 h10 => by rw [f'.lane x (by simp [h8, h9, h10]) 0 (by decide), l₁], by rw [f'.mem, m₁],
      by rw [f'.rd, rd₁], by rw [f'.wr, wr₁]⟩

theorem remTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOk (hk s₀) P) {e : Nat} {s : State} (hI : EInvTo s₀ P e s) (hex : nb s₀ - 16 * (e - 1) < 32)
    (hne : nb s₀ ≠ 16 * e) (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa remTo s (EPostTo s₀) := by
  have hd := hp.toD
  have hw := hp.wrap_o
  have hws := hp.wrap_s
  have hwp := hp.wrap_p
  have h1e := hI.one
  have hle := hI.a.le
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have epp : pp (dst s₀) = pp s₀ := dst_gpr_ne s₀ (by decide)
  have eci : ciph (dst s₀) = ciph s₀ := by
    simp only [ciph, sch, nr, kp, dst_mem, dst_gpr_ne s₀ (show Reg.rdi ≠ .r8 by decide),
      dst_gpr_ne s₀ (show Reg.rsi ≠ .r8 by decide)]
  have ecb : cb (dst s₀) = cb s₀ := by
    simp only [cb, cp, dst_mem, dst_gpr_ne s₀ (show Reg.rdx ≠ .r8 by decide)]
  -- The `r` blocks after the `16 e` encrypted.
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by omega
  have hr15 : r ≤ 15 := by omega
  have hr9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r) := by rw [hI.r9]; congr 1; omega
  have hrax : s.gpr .rax = cp s₀ := hI.rax
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show remTo = .seq (.block remSetup) (.seq ksSel
      (.seq (.block (([.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)] : List Instr) ++
          ([.alu .add .r8 (.reg .rdx)] : List Instr) ++ Impl.Gcm.X86_64.StitchAvx.zero))
        (.seq (.loop (.block (remBody .r8 ++ remNext)) .ne)
          (.block (Impl.Gcm.X86_64.StitchAvx.reduceHash ++ storeY))))) from rfl]
  -- The counter after all the blocks, and the powers of the `r` blocks.
  refine WP.seq (WP.mono (WP.hkeep (by decide) (remSetup_ok s hr1 hr15 hr9
    (by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide))
    (by rw [hrax, hI.a.wr]; exact in_sub_int hp.c_in (by omega))))
    fun s₁ ⟨⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  have e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hrax, e0] at m₁
  rw [hr11] at ax₁
  have gk₁ : ∀ q, q ≠ .r10 → q ≠ .rax → s₁.gpr q = s.gpr q := g₁
  have cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  have hfr₁ : Frame [oR s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cw
  have hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [gk₁ _ (by decide) (by decide)]; exact hI.a.rdi
  have hCache₁ := hCache.keep hh₁ (keys_of hd hrdi₁ (by rw [rd₁]; exact hI.a.rd) (by rw [wr₁]; exact hI.a.wr) hfr₁)
  -- The last group of the output, hashed while the keystream is computed.
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctbT s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (op s₀).toNat + 256 * (e - 1) := hI.rdx
  have hE₁ : GEnv (dst s₀) 0 a X P s₁ :=
    { rdx := by rw [gk₁ _ (by decide) (by decide)]
      r11 := by rw [gk₁ _ (by decide) (by decide), hr11, epp]
      xs := fun i _ hi => by
        rw [show a + BitVec.ofNat 64 (16 * i) = oAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega), m₁,
          show cp s₀ = (cR s₀).base from rfl,
          blockAt_writeW_sep' (hp.o_c.sub_left (Offset.sub_base _ (by omega))) rfl,
          hI.a.blocks _ (by omega)]
      pv := fun k hk l hl => by
        rw [epp, m₁, Mem.readW_writeW_sep ((hp.p_c.sub_left (Offset.sub_base _ (by omega))).sep
          (Region.contains_self _ _) cw) (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = op s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.o_in (by omega))
      inp := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr, epp]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  have hQ₁ : QG (dst s₀) (fun _ => 0) a X P yl 1 s₁ :=
    ⟨hE₁, fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun h => absurd h (by decide), fun l hl => by rw [z₁ _ (by decide) l hl]⟩⟩
  refine WP.seq (WP.mono (ksSel_ok hd hr1 hr15 (QG (dst s₀) (fun _ => 0) a X P yl)
    (gq_ok (s₀ := dst s₀) (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.ksR hd (g := e - 1) (by show 16 * (e - 1) + 16 ≤ nb s₀; omega) ha h hg
      hrd hwr hl hf)
    (c := 16 * e) a10₁ (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.ctr l hl)
    (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.msk l hl)
    (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.inc l hl) hrdi₁
    (by rw [gk₁ _ (by decide) (by decide), dst_gpr_ne s₀ (by decide)]; exact hI.a.rsi)
    (by rw [gk₁ _ (by decide) (by decide)]; exact hr11)
    (by rw [rd₁]; exact hI.a.rd) (by rw [wr₁]; exact hI.a.wr) hfr₁ hCache₁ hQ₁)
    fun s₂ ⟨q₂, ks₂, g₂, rd₂, wr₂, l₂, f₂⟩ => ?_)
  obtain ⟨_, h1₂, y₂⟩ := q₂
  rw [ite_t (by decide)] at y₂
  -- `Y` after the groups.
  have hY₂ : s₂.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctbT s₀)) := by
    rw [← State.zlane_lt2 _ _ (by decide), y₂.1, hf X yl hI.y1,
      show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega, VG.Proof.Gcm.X86_64.Stitch.ghash_append16, ← hI.y]
  -- `rdx` at the `r` output blocks, `r8` at the plaintext's, `r10 = 0`, the products cleared.
  refine WP.seq (WP.mono (remPreTo_ok s₂) fun s₃ ⟨d₃, r8₃, z₃, g₃, p₃, l₃, m₃, rd₃, wr₃⟩ => ?_)
  have hA : s₃.gpr .rdx = oAddr s₀ (16 * e) := by
    rw [d₃, g₂, gk₁ _ (by decide) (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (show a.toNat + 256 < 2 ^ 64 by omega), BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 16 * (16 * e) < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    show a.toNat + 256 = _
    omega
  have hS : s₃.gpr .r8 = sAddr s₀ (16 * e) := by
    rw [r8₃, ← d₃, hA, g₂, gk₁ _ (by decide) (by decide), hI.a.r8, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  let E : REnv := REnv.mk r .r8 (sAddr s₀ (16 * e)) (oAddr s₀ (16 * e)) (pp s₀)
    (pp s₀ + BitVec.ofNat 64 (256 - 16 * r)) s₃.mem s₃.gpr s₃.rd s₃.wr (s₃.lane .xmm2 0)
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁, hI.a.rd]
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁, hI.a.wr]
  have gk₃ : ∀ q, q ≠ .rdx → q ≠ .r10 → q ≠ .rax → q ≠ .r8 → s₃.gpr q = s.gpr q := fun q h1 h2 h3 h4 => by
    rw [g₃ q h1 h2 h4, g₂, gk₁ q h2 h3]
  have hE : E.Ok :=
    { r1 := hr1, r15 := hr15, gS := hS, gA := hA,
      gP := by show s₃.gpr .r11 = _; rw [gk₃ _ (by decide) (by decide) (by decide) (by decide), hr11]
      gW := by show s₃.gpr .rax = _; rw [g₃ _ (by decide) (by decide) (by decide), g₂, ax₁]
      src9 := by show Reg.r8 ≠ Reg.r9; decide, src10 := by show Reg.r8 ≠ Reg.r10; decide
      inS := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (sAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.s_in (by omega)
      inK := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [hrd₃, hwr₃]
        exact in_rdwr (in_sub hp.p_in (by omega))
      inD := fun j (hj : j < r) => by
        show InRegions s₃.wr (oAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.o_in (by omega)
      inW := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega))
      dS := fun j (hj : j < r) i hi => by
        show Region.Disjoint ⟨sAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨oAddr s₀ (16 * e), 16 * i⟩
        rw [Offset.add_add]
        exact (hp.s_o.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
      dK := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (768 + 16 * j), 16⟩ ⟨oAddr s₀ (16 * e), 16 * r⟩
        exact (hp.o_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
      dW := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨oAddr s₀ (16 * e), 16 * r⟩
        rw [Offset.add_add]
        exact (hp.o_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)) }
  have hI₃ : RInv E 0 s₃ :=
    { le := Nat.zero_le _, r10 := z₃
      r9 := by
        show s₃.gpr .r9 = _
        rw [gk₃ _ (by decide) (by decide) (by decide) (by decide), hr9, Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := p₃
      y := rfl
      m0 := by
        rw [l₃ _ (by decide) (by decide) (by decide), ← State.zlane_lt2 _ _ (by decide),
          l₂ _ (by decide) (by decide) (by decide) (by decide) 0 (by decide), z₁ _ (by decide) 0 (by decide)]
        exact hI.a.msk 0 (by decide)
      m1 := by
        rw [l₃ _ (by decide) (by decide) (by decide), ← State.zlane_lt2 _ _ (by decide)]
        exact h1₂ 0 (by decide) }
  refine WP.seq (WP.mono (remLoop_ok hE hI₃) fun s₄ hI₄ => ?_)
  -- The products reduced into `Y`, and `Y` stored.
  rw [WP.block_append_iff]
  refine WP.mono (Gcm.X86_64.StitchAvx.reduceHash_ok s₄ hI₄.m1) fun s₅ ⟨y₅, f₅⟩ => ?_
  have hrcx : s₅.gpr .rcx = yp s₀ := by
    rw [f₅.gpr, hI₄.gpr _ (by decide) (by decide)]
    show s₃.gpr .rcx = _
    rw [gk₃ _ (by decide) (by decide) (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (Gcm.X86_64.StitchZ.store16Z_ok .xmm2 .xmm2 .rcx s₅
    (by rw [f₅.lane _ (by decide) 0 (by decide)]; exact hI₄.m0)
    (by rw [hrcx, f₅.wr, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.y_in))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx, f₅.mem] at m₆
  have hnb : nb s₀ = 16 * e + r := by omega
  -- What the stages keep of the memory before them.
  have toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) → Region.Disjoint ⟨p, 16⟩ (ksR s₀) →
      blockAt s₃.mem p = blockAt s.mem p := fun p hc hk => by
    rw [m₃, blockAt_frame f₂ (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hk), m₁,
      show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  have ksO : ∀ k, k < nb s₀ → Region.Disjoint ⟨oAddr s₀ k, 16⟩ (ksR s₀) := fun k hk =>
    (hp.o_p.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  have cO : ∀ k, k < nb s₀ → Region.Disjoint ⟨oAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.o_c.sub_left (Offset.sub_base _ (by omega))
  have ksS : ∀ k, k < nb s₀ → Region.Disjoint ⟨sAddr s₀ k, 16⟩ (ksR s₀) := fun k hk =>
    (hp.s_p.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  have cS : ∀ k, k < nb s₀ → Region.Disjoint ⟨sAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.s_c.sub_left (Offset.sub_base _ (by omega))
  have hX : ∀ j < r, E.X j = ctbT s₀ (16 * e + j) := fun j hj => by
    have hk : 16 * e + j < nb s₀ := by omega
    show blockAt s₃.mem (sAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₃.mem (pp s₀ + BitVec.ofNat 64 (768 + 16 * j)) = _
    have k₂ := ks₂ j hj
    rw [epp, eci, ecb] at k₂
    rw [Offset.add_add, ← Nat.mul_add, toS _ (cS _ hk) (ksS _ hk), hI.a.src hp hk, m₃, k₂]
  -- The blocks.
  have hb₄ : ∀ k < nb s₀, blockAt s₄.mem (oAddr s₀ k) = ctbT s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame hI₄.frame (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          show Region.Disjoint _ ⟨oAddr s₀ (16 * e), 16 * r⟩
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)),
        toS _ (cO k hk) (ksO k hk), hI.a.blocks k hke]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega⟩
      have hj : j < r := by omega
      have ct := hI₄.ct j hj
      have eD : E.aD j = oAddr s₀ (16 * e + j) := by
        show oAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j) = _
        rw [Offset.add_add, ← Nat.mul_add]
      rw [eD] at ct
      rw [ct, hX j hj]
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
  have yO : ∀ k < nb s₀, Region.Disjoint ⟨oAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.o_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < nb s₀, blockAt s₆.mem (oAddr s₀ k) = ctbT s₀ k := fun k hk => by
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yO k hk) rfl, hb₄ k hk]
  have fA : ∀ R : Region, R.Disjoint (oR s₀) → ∀ r' ∈ [(⟨E.A, 16 * E.r⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega))
  refine ⟨blocks_ctr32To hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show blockAt s₆.mem (cp s₀) = _
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl,
      blockAt_frame hI₄.frame (fA _ hp.o_c.symm), show E.m = s₃.mem from rfl, m₃,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.p_c.symm.sub_right (Offset.sub_base _ (by omega))),
      m₁, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), hI.a.ctr 0 (by decide),
      Nat.add_zero, VG.Proof.Aes.X86_64.AesNi.rep_add, hnb]
  · show blockAt s₆.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₆.mem (op s₀) (nb s₀))
    have hbl : blocksAt s₆.mem (op s₀) (nb s₀) = (List.range (nb s₀)).map (ctbT s₀) := by
      simp only [blocksAt]
      exact List.map_congr_left fun k hk => hb k (by simpa using hk)
    rw [hbl, m₆, VG.Proof.Gcm.X86_64.blockAt_store, y₅, hI₄.prod, accR_congr _ r hX hT, hr r hr1 hr15,
      show E.y = s₃.lane .xmm2 0 from rfl, l₃ _ (by decide) (by decide) (by decide), hY₂, hnb,
      List.range_add, List.map_append, List.map_map]
    simp only [ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₆.mem
    have F0 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₀.mem s.mem := hI.a.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    have F1 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    have F2 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₁.mem s₃.mem := by
      rw [m₃]
      exact f₂.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega)⟩
    have F3 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₃.mem s₄.mem := hI₄.frame.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨oR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega)⟩
    rw [m₆]
    exact (((F0.trans F1).trans F2).trans F3).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4 h5
    show s₆.gpr q = _
    rw [g₆, f₅.gpr, hI₄.gpr q h4 h5]
    show s₃.gpr q = _
    rw [gk₃ q h2 h5 h1 h3]
    exact hI.gpr q h1 h2 h3 h4 h5
  · show s₆.rd = _
    rw [rd₆, f₅.rd, hI₄.rd]; exact hrd₃
  · show s₆.wr = _
    rw [wr₆, f₅.wr, hI₄.wr]; exact hwr₃

/-- The end of `encR`: the last group, and the blocks after it if any. -/
theorem tailRTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOk (hk s₀) P) {e : Nat} {s : State} (hI : EInvTo s₀ P e s) (hex : nb s₀ - 16 * (e - 1) < 32)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (tailR remTo) s (EPostTo s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have h1e := hI.one
  have hle := hI.a.le
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp16_ok s)) fun s₁ ⟨⟨zf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₁ := hI.of_eq g l m rd wr
  have hz : (s.gpr .r9 - 16 == 0) = decide (nb s₀ = 16 * e) := by
    rw [hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega) (by omega)]
    by_cases h : nb s₀ = 16 * e
    · rw [show nb s₀ - 16 * (e - 1) - 16 = 0 by omega, decide_eq_true h]; rfl
    · have : BitVec.ofNat 64 (nb s₀ - 16 * (e - 1) - 16) ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega
      rw [beq_false_of_ne this, decide_eq_false h]
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, zf, hz]) (fun h => ?_) (fun h => ?_)
  · exact finalTo_ok hp hf (by simpa using h) hI₁
  · exact remTo_ok hp hf hr hI₁ hex (by simpa using h) (hCache.keep hh (hI₁.a.keys hp))

/-- `encR` after the setup, for any number of blocks from 16 on. -/
theorem encTailRGTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block}
    (hf : FinOk (hk s₀) P) (hr : RemOk (hk s₀) P)
    {bigC : Prog isa} (hbig : ∀ s, 256 ≤ nb s₀ → EInvTo s₀ P 1 s → VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s →
      WP isa bigC s fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s')
    {s : State} (hR : StitchZTo.ReadyTo s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq Impl.Gcm.X86_64.StitchZHTo.firstTo (.seq (.block [.alu .cmp .r9 (.imm 256)])
      (.seq (.ite .b (.block []) bigC) (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop Impl.Gcm.X86_64.StitchZHTo.bodyTo .ae)) (tailR remTo)))))) s
      (EPostTo s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (firstTo_ok hp hR hCache) fun s₂ ⟨hI₂, hCache₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (Gcm.X86_64.StitchZ.cmp_ok s₂ 256 256 (by decide)))
    fun s₃ ⟨⟨hcf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₃ := hI₂.of_eq g l m rd wr
  have hCache₃ := hCache₂.keep hh (hI₃.a.keys hp)
  rw [hI₂.r9, VG.Proof.Gcm.X86_64.Pclmul.toNat_ofNat_lt (by omega),
    VG.Proof.Gcm.X86_64.Pclmul.toNat_ofNat_lt (by decide)] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, EInvTo s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * (1 - 1) < 256))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨1, hI₃, hCache₃⟩)
    (fun h => hbig _ (by simp at h; omega) hI₃ hCache₃)) fun s₄ ⟨e, hI₄, hCache₄⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (StitchZTo.cmpE_ok hI₄)) fun s₅ ⟨⟨hI₅, hcf₅⟩, hh₅⟩ => ?_)
  exact WP.seq (WP.mono (loopERTo_ok hp hf hI₅ hcf₅ (hCache₄.keep hh₅ (hI₅.a.keys hp)))
    fun s₆ ⟨e, hex, hI₆, hC₆⟩ => tailRTo_ok hp hf hr hI₆ hex hC₆)

end VG.Proof.Gcm.X86_64.StitchZHTo
