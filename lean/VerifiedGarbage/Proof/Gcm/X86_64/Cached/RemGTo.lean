module
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGLanes

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemG
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48To
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Ks
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.LoopTo
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The blocks after the last group, out of place, as a masked group

`remGTo_ok`: `StitchZHTo.remTo` is `StitchZH.remG` reading the `r` blocks
after the last group from the plaintext (at `rdx + r8`, `r8` holding
`src - dst`) and writing them to the output: the counter after all the
blocks (`remSetup_ok`), the `r` blocks encrypted as a masked group while the
last group of the output is hashed (`ksSelG_ok`, on the in-place view
`dst s₀`), and their products reduced into `Y`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR addr_eq in_sub in_sub_int in_rdwr blockAt_writeW_sep' ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeY)
open VG.Impl.Gcm.X86_64.Slot (storeCtr)
open VG.Impl.Gcm.X86_64.StitchZ (gq lastG)
open VG.Impl.Gcm.X86_64.StitchZH (ksSelG remSetupM tailR)
open VG.Impl.Gcm.X86_64.StitchZHTo (remTo)
open VG.Proof.Gcm.X86_64.StitchZ (GEnv QG gq_ok FinOk yNew)
open VG.Proof.Gcm.X86_64.StitchZTo (EInvTo dst dst_gpr_ne dst_mem sAddr oAddr ctbT blocks_ctr32To finalTo_ok)
open VG.Proof.Gcm.X86_64.StitchZH (RemOkG laneAccG laneAccG_congr ksSelG_ok remSetupM_ok keys_of cmp16_ok)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- `add rdx, 256` and `add r8, rdx`. -/
theorem addRdxR8_ok (t : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .add .r8 (.reg .rdx)]) t fun t' =>
      t'.gpr .rdx = t.gpr .rdx + 256 ∧ t'.gpr .r8 = t.gpr .r8 + (t.gpr .rdx + 256) ∧
      (∀ q, q ≠ .rdx → q ≠ .r8 → t'.gpr q = t.gpr q) ∧
      (∀ x l, t'.zlane x l = t.zlane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, State.setReg, e256, reduceCtorEq, ↓reduceIte,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun q h1 h2 => by simp only [h1, h2, ↓reduceIte], fun _ _ => rfl, trivial, trivial,
    trivial⟩

theorem remGTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOkG (hk s₀) P) {e : Nat} {s : State} (hI : EInvTo s₀ P e s) (hex : nb s₀ - 16 * (e - 1) < 32)
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
  have hr1 : 1 ≤ r := by omega_using [hne, hle, hr_def]
  have hr15 : r ≤ 15 := by omega_using [hex, h1e, hr_def]
  have hr9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r) := by rw [hI.r9]; congr 1; omega_using [h1e, hr_def, hr1]
  have hrax : s.gpr .rax = cp s₀ := hI.rax
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show remTo = .seq (.block remSetupM) (.seq (ksSelG [.alu .add .r8 (.reg .rdx)] .r8) (.block storeY)) from rfl]
  -- The counter after all the blocks, and the powers of the `r` blocks.
  refine WP.seq (WP.mono (WP.hkeep (by decide) (remSetupM_ok s (C := cb s₀) (c := 16 * e) hr1 hr15 hr9
    (by rw [hr11]; exact hI.a.slot)
    (by rw [hr11, hI.a.rd, hI.a.wr]; exact in_rdwr (in_sub hp.p_in (by decide)))
    (by rw [hrax, hI.a.wr]; exact hp.c_in)
    (by rw [hrax, hr11]; exact hp.p_c.symm.sub_right (Gcm.X86_64.StitchZ.slot_sub s₀))))
    fun s₁ ⟨⟨b₁, fc₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  rw [hrax] at b₁ fc₁
  have fcR : ∀ {R : Region}, Region.Disjoint R (cR s₀) → ∀ r ∈ [(⟨cp s₀, 16⟩ : Region)], Region.Disjoint R r :=
    fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
  have fc₁' : Frame [cR s₀] s.mem s₁.mem := fc₁
  rw [hr11] at ax₁
  have gk₁ : ∀ q, q ≠ .r10 → q ≠ .rax → s₁.gpr q = s.gpr q := g₁
  have hfr₁ : Frame [oR s₀, pR s₀, cR s₀] s₀.mem s₁.mem :=
    (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).trans
      (fc₁'.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
  have hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [gk₁ _ (by decide) (by decide)]; exact hI.a.rdi
  have hCache₁ := hCache.keep hh₁ (keys_of hd hrdi₁ (by rw [rd₁]; exact hI.a.rd) (by rw [wr₁]; exact hI.a.wr) hfr₁)
  -- The last group of the output, hashed while the `r` blocks are encrypted.
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctbT s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (op s₀).toNat + 256 * (e - 1) := hI.rdx
  have hE₁ : GEnv (dst s₀) 0 a X P s₁ :=
    { rdx := by rw [gk₁ _ (by decide) (by decide)]
      r11 := by rw [gk₁ _ (by decide) (by decide), hr11, epp]
      xs := fun i _ hi => by
        rw [show a + BitVec.ofNat 64 (16 * i) = oAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega_using [ha]),
          blockAt_frame fc₁ (fcR (hp.o_c.sub_left (Offset.sub_base _ (by omega_using [h1e, hle, hi])))),
          hI.a.blocks _ (by omega_using [h1e, hi])]
      pv := fun k hk l hl => by
        rw [epp, fc₁.readW (Region.contains_self _ _) (fcR (hp.p_c.sub_left (Offset.sub_base _ (by omega_using [hk, hl]))))
          (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = op s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega_using [ha])]
        exact in_rdwr (in_sub hp.o_in (by omega_using [h1e, hle, hk]))
      inp := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr, epp]
        exact in_rdwr (in_sub_int hp.p_in (by omega_using [hk]))
      m0 := fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  have hQ₁ : QG (dst s₀) (fun _ => 0) a X P yl 1 s₁ :=
    ⟨hE₁, fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun h => absurd h (by decide), fun l hl => by rw [z₁ _ (by decide) l hl]⟩⟩
  -- Where the `r` blocks, their output and their powers are.
  let A := oAddr s₀ (16 * e)
  let S := sAddr s₀ (16 * e)
  let W := pp s₀ + BitVec.ofNat 64 (256 - 16 * r)
  have hA : a + 256 = A := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (show a.toNat + 256 < 2 ^ 64 by omega_using [hne, hw, h1e, hle, ha]), BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 16 * (16 * e) < 2 ^ 64 by omega_using [hne, hws, hle]), Nat.mod_eq_of_lt (by omega_using [hne, hw, hle])]
    omega_using [h1e, ha]
  have hS : s.gpr .r8 + A = S := by
    show s.gpr .r8 + oAddr s₀ (16 * e) = sAddr s₀ (16 * e)
    rw [hI.a.r8]
    show sp s₀ - op s₀ + (op s₀ + BitVec.ofNat 64 (16 * (16 * e))) = sp s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [← BitVec.add_assoc, BitVec.sub_add_cancel]
  have hrd₁ : s₁.rd = s₀.rd := by rw [rd₁, hI.a.rd]
  have hwr₁ : s₁.wr = s₀.wr := by rw [wr₁, hI.a.wr]
  have eA : ∀ j, A + BitVec.ofNat 64 (16 * j) = oAddr s₀ (16 * e + j) := fun j => by
    show oAddr s₀ (16 * e) + _ = _
    rw [Offset.add_add, ← Nat.mul_add]
  have eS : ∀ j, S + BitVec.ofNat 64 (16 * j) = sAddr s₀ (16 * e + j) := fun j => by
    show sAddr s₀ (16 * e) + _ = _
    rw [Offset.add_add, ← Nat.mul_add]
  have hQ10 : ∀ t, QG (dst s₀) (fun _ => 0) a X P yl 10 t → (∀ l < 4, t.zlane .xmm1 l = poly) ∧
      ∀ l < 4, t.zlane .xmm2 l = if l = 0 then yNew X P yl else 0 := fun t ⟨_, h1, h2⟩ => by
    rw [ite_t (by decide)] at h2
    refine ⟨h1, fun l hl => ?_⟩
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · exact h2.1
    · rw [ite_eq_right_iff.2 (fun h => absurd h (by omega_using [hl0]))]; exact h2.2 l hl0 hl
  refine WP.seq (WP.mono (ksSelG_ok hd hr1 hr15 (QG (dst s₀) (fun _ => 0) a X P yl)
    (gq_ok (s₀ := dst s₀) (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide)) [.alu .add .r8 (.reg .rdx)] .r8 (by decide) (by decide) (by decide)
    (A := A) (S := S) (W := W) (D := fun n => blockAt s₁.mem (S + BitVec.ofNat 64 (16 * n)))
    (T := fun n => s₁.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128) (c := 16 * e)
    (fun t ht => WP.mono (addRdxR8_ok t) fun t' ⟨d', r8', g', l', m', rd', wr'⟩ =>
      ⟨by rw [d', ht, gk₁ _ (by decide) (by decide)]; exact hA,
        by rw [r8', ht, gk₁ _ (by decide) (by decide), gk₁ _ (by decide) (by decide)]
           show s.gpr .r8 + (a + 256) = S
           rw [hA]; exact hS,
        fun q h1 h2 => g' q h1 h2, l', m', rd', wr'⟩)
    hQ10 a10₁ (by rw [epp, ecb]; exact hI.a.slot.frame fc₁ (fcR (hp.p_c.sub_left (Gcm.X86_64.StitchZ.slot_sub s₀))))
    (by rw [gk₁ _ (by decide) (by decide), hr11, epp])
    (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.msk l hl) hrdi₁
    (by rw [gk₁ _ (by decide) (by decide), dst_gpr_ne s₀ (by decide)]; exact hI.a.rsi)
    (by rw [rd₁]; exact hI.a.rd) (by rw [wr₁]; exact hI.a.wr) hfr₁ hCache₁ hQ₁
    (by rw [gk₁ _ (by decide) (by decide)]; exact hr9) ax₁ (fun _ _ => rfl) (fun _ _ => rfl)
    (by rw [hrd₁, hwr₁, show S = sp s₀ + BitVec.ofNat 64 (16 * (16 * e)) from rfl]
        exact in_sub hp.s_in (by omega_using [hr_def, hr1]))
    (by rw [hwr₁, show A = op s₀ + BitVec.ofNat 64 (16 * (16 * e)) from rfl]
        exact in_sub hp.o_in (by omega_using [hr_def, hr1]))
    (by rw [hrd₁, hwr₁]; exact in_rdwr (in_sub hp.p_in (by omega_using [hr15])))
    (fun n q' hq hn => by
      rw [eS, show A + BitVec.ofNat 64 (64 * q') = op s₀ + BitVec.ofNat 64 (16 * (16 * e) + 64 * q') by
        show op s₀ + BitVec.ofNat 64 (16 * (16 * e)) + _ = _; rw [Offset.add_add]]
      exact (hp.s_o.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)))
    (fun n hn => by
      show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * n), 16⟩
        ⟨oAddr s₀ (16 * e), 16 * r⟩
      rw [Offset.add_add]
      exact (hp.o_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))))
    fun s₂ ⟨b₂, f₂, y₂, _, g₂, rd₂, wr₂, z₂⟩ => ?_)
  rw [eci, ecb] at b₂ y₂
  -- `Y` after the groups.
  have hY : yNew X P yl = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctbT s₀)) := by
    rw [hf X yl hI.y1, show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega_using [h1e],
      VG.Proof.Gcm.X86_64.Stitch.ghash_append16, ← hI.y]
  -- `Y` stored.
  have hrcx : s₂.gpr .rcx = yp s₀ := by
    rw [g₂ _ (by decide) (by decide) (by decide), gk₁ _ (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have m0₂ : s₂.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), z₂ _ (by decide) (by decide) (by decide) (by decide) 0 (by decide),
      z₁ _ (by decide) 0 (by decide)]
    exact hI.a.msk 0 (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (Gcm.X86_64.StitchZ.store16Z_ok .xmm2 .xmm2 .rcx s₂ m0₂
    (by rw [hrcx, wr₂, hwr₁]; exact hp.y_in))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx] at m₆
  have hnb : nb s₀ = 16 * e + r := by omega_using [hr_def, hr1]
  -- What the setup keeps of the memory before it.
  have toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) → blockAt s₁.mem p = blockAt s.mem p := fun p hc => by
    exact blockAt_frame fc₁ (fcR hc)
  have cO : ∀ k, k < nb s₀ → Region.Disjoint ⟨oAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.o_c.sub_left (Offset.sub_base _ (by omega_using [hk]))
  have cS : ∀ k, k < nb s₀ → Region.Disjoint ⟨sAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.s_c.sub_left (Offset.sub_base _ (by omega_using [hk]))
  -- The `r` blocks, encrypted.
  have hX : ∀ j < r, blockAt s₁.mem (S + BitVec.ofNat 64 (16 * j)) ^^^
      ciph s₀ (Nat.repeat inc32 (16 * e + j) (cb s₀)) = ctbT s₀ (16 * e + j) := fun j hj => by
    have hk : 16 * e + j < nb s₀ := by omega_using [hnb, hj]
    rw [eS, toS _ (cS _ hk), hI.a.src hp hk]
  -- The blocks.
  have hb₂ : ∀ k < nb s₀, blockAt s₂.mem (oAddr s₀ k) = ctbT s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame f₂ (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (.inl (by omega_using [hke])) (by omega_using [ha, hke]) (by omega_using [hws, hnb])),
        toS _ (cO k hk), hI.a.blocks k hke]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega_using [hke]⟩
      have hj : j < r := by omega_using [hnb, hk]
      rw [← eA, b₂ j hj, hX j hj]
  have hT : ∀ j < r, s₁.mem.readW (W + BitVec.ofNat 64 (16 * j)) 128 = P ((16 - r + j) / 4) ((16 - r + j) % 4) :=
    fun j hj => by
      have hm : 16 - r + j < 16 := by omega_using [hr15, hj]
      rw [Offset.add_add, show 256 - 16 * r + 16 * j = 64 * ((16 - r + j) / 4) + 16 * ((16 - r + j) % 4) by omega_using [],
        fc₁.readW (Region.contains_self _ _) (fcR (hp.p_c.sub_left (Offset.sub_base _ (by omega_using [hm]))))
          (by decide)]
      exact hI.pw _ (by omega_using [hm]) _ (by omega_using [])
  have yO : ∀ k < nb s₀, Region.Disjoint ⟨oAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.o_y.sub_left (Offset.sub_base _ (by omega_using [hk]))
  have hb : ∀ k < nb s₀, blockAt s₆.mem (oAddr s₀ k) = ctbT s₀ k := fun k hk => by
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yO k hk) rfl, hb₂ k hk]
  refine ⟨blocks_ctr32To hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show blockAt s₆.mem (cp s₀) = _
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.o_c.symm.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_using [hnb]))),
      b₁, hnb]
  · show blockAt s₆.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₆.mem (op s₀) (nb s₀))
    have hbl : blocksAt s₆.mem (op s₀) (nb s₀) = (List.range (nb s₀)).map (ctbT s₀) := by
      simp only [blocksAt]
      exact List.map_congr_left fun k hk => hb k (by simpa using hk)
    have cg : ∀ l, laneAccG (fun n => blockAt s₁.mem (S + BitVec.ofNat 64 (16 * n)) ^^^
        ciph s₀ (Nat.repeat inc32 (16 * e + n) (cb s₀))) (fun n => s₁.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128)
        (yNew X P yl) l r = laneAccG (fun j => ctbT s₀ (16 * e + j)) (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4))
        (yNew X P yl) l r := fun l => laneAccG_congr _ l r hX hT
    rw [hbl, m₆, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (show 0 < 2 by decide), y₂, cg 0, cg 1,
      cg 2, cg 3, hr r hr1 hr15, hY, hnb, List.range_add, List.map_append, List.map_map]
    simp only [ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₆.mem
    have F0 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₀.mem s.mem := hI.a.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    have F1 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s.mem s₁.mem := by
      exact fc₁'.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    have F2 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₁.mem s₂.mem := f₂.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨oR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_using [hnb])⟩
    rw [m₆]
    exact ((F0.trans F1).trans F2).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4 h5
    show s₆.gpr q = _
    rw [g₆, g₂ q h5 h2 h3, gk₁ q h5 h1]
    exact hI.gpr q h1 h2 h3 h4 h5
  · show s₆.rd = _
    rw [rd₆, rd₂]; exact hrd₁
  · show s₆.wr = _
    rw [wr₆, wr₂]; exact hwr₁

/-- The end of `encR`: the last group, and the blocks after it if any. -/
theorem tailRTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOkG (hk s₀) P) {e : Nat} {s : State} (hI : EInvTo s₀ P e s) (hex : nb s₀ - 16 * (e - 1) < 32)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (tailR remTo) s (EPostTo s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have h1e := hI.one
  have hle := hI.a.le
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp16_ok s)) fun s₁ ⟨⟨zf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₁ := hI.of_eq g l m rd wr
  have hz : (s.gpr .r9 - 16 == 0) = decide (nb s₀ = 16 * e) := by
    rw [hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega_using [h1e, hle]) (by omega_using [hn])]
    by_cases h : nb s₀ = 16 * e
    · rw [show nb s₀ - 16 * (e - 1) - 16 = 0 by omega_using [h], decide_eq_true h]; rfl
    · have : BitVec.ofNat 64 (nb s₀ - 16 * (e - 1) - 16) ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega_using [h1e, hle, h, this, h0]
      rw [beq_false_of_ne this, decide_eq_false h]
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, zf, hz]) (fun h => ?_) (fun h => ?_)
  · exact finalTo_ok hp hf (by simpa using h) hI₁
  · exact remGTo_ok hp hf hr hI₁ hex (by simpa using h) (hCache.keep hh (hI₁.a.keys hp))

/-- `encR` after the setup, for any number of blocks from 16 on. -/
theorem encTailRGTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block}
    (hf : FinOk (hk s₀) P) (hr : RemOkG (hk s₀) P)
    {bigC : Prog isa} {i : BitVec 32} (t : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 t)
    (ht : t < 2 ^ 64) (hbig : ∀ s, t ≤ nb s₀ → EInvTo s₀ P 1 s → VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s →
      WP isa bigC s fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s')
    {s : State} (hR : StitchZTo.ReadyTo s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq Impl.Gcm.X86_64.StitchZHTo.firstTo (.seq (.block [.alu .cmp .r9 (.imm i)])
      (.seq (.ite .b (.block []) bigC) (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop Impl.Gcm.X86_64.StitchZHTo.bodyTo .ae)) (tailR remTo)))))) s
      (EPostTo s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (firstTo_ok hp hR hCache) fun s₂ ⟨hI₂, hCache₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep rfl (Gcm.X86_64.StitchZ.cmp_ok s₂ i t hi))
    fun s₃ ⟨⟨hcf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₃ := hI₂.of_eq g l m rd wr
  have hCache₃ := hCache₂.keep hh (hI₃.a.keys hp)
  rw [hI₂.r9, VG.Proof.Gcm.X86_64.Pclmul.toNat_ofNat_lt (by omega_using [hn]),
    VG.Proof.Gcm.X86_64.Pclmul.toNat_ofNat_lt ht] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, EInvTo s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * (1 - 1) < t))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨1, hI₃, hCache₃⟩)
    (fun h => hbig _ (by simp at h; omega_using [h]) hI₃ hCache₃)) fun s₄ ⟨e, hI₄, hCache₄⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (StitchZTo.cmpE_ok hI₄)) fun s₅ ⟨⟨hI₅, hcf₅⟩, hh₅⟩ => ?_)
  exact WP.seq (WP.mono (loopERTo_ok hp hf hI₅ hcf₅ (hCache₄.keep hh₅ (hI₅.a.keys hp)))
    fun s₆ ⟨e, hex, hI₆, hC₆⟩ => tailRTo_ok hp hf hr hI₆ hex hC₆)
end VG.Proof.Gcm.X86_64.StitchZHTo
