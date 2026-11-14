module
public import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
import VerifiedGarbage.Proof.Framework.X86_64.Avx512

import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Interleaved counter mode and GHASH: the setup

`storesK_ok`: `storesK base rs j` stores the registers `rs` to
`base + 32 (j + i)`. `setupC_ok`: the end of the setup loads `Y`, and makes
the counter pair, the increment and the last round key's address. The
powers the setup computes before (`setupG_ok`) are in the field, in
`Stitch/Ok.lean`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (storesK setupC)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Proof.Aes.X86_64.Vaes (extract_lo extract_hi)
open VG.Spec.Gcm (Block blockAt inc32)

theorem storesK_ok (base : Reg) : ∀ (rs : List XReg) (j : Nat) (s : State),
    (∀ k < rs.length, InRegions s.wr (s.gpr base + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32) →
    (s.gpr base).toNat + 32 * (j + rs.length) ≤ 2 ^ 64 →
    WP isa (.block (storesK base rs j)) s fun s' =>
      (∀ k (h : k < rs.length), ∀ l < 2,
        s'.mem.readW (s.gpr base + BitVec.ofNat 64 (32 * (j + k) + 16 * l)) 128 = s.lane rs[k] l) ∧
      Frame [⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * rs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.lane r l = s.lane r l)
  | [], _, s, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | r :: rs, j, s, hin, hw => by
    simp only [List.length_cons] at hin hw
    have ha : s.gpr base + BitVec.ofInt 64 ((32 * j : Nat) : Int) = s.gpr base + BitVec.ofNat 64 (32 * j) := by
      rw [BitVec.ofInt_natCast]
    have hin0 := hin 0 (by omega_arith)
    rw [Nat.add_zero, ha] at hin0
    let s₁ := s.setMem (s.mem.writeW (s.gpr base + BitVec.ofNat 64 (32 * j)) (s.ymm r))
    rw [storesK, WP.block_cons_iff]
    refine ⟨s₁, by
      simp only [isa, exec, State.store256_eq, VG.Proof.Gcm.X86_64.Pclmul.ea_at, ha, hin0, ite_true]; rfl, ?_⟩
    have hg₁ : s₁.gpr = s.gpr := by simp [s₁]
    refine WP.mono (storesK_ok base rs (j + 1) s₁ (fun k hk => by
        rw [hg₁, show s₁.wr = s.wr by simp [s₁], show j + 1 + k = j + (k + 1) by omega_arith]; exact hin (k + 1) (by omega_arith))
      (by rw [hg₁]; omega_arith)) fun s' ⟨hv, hf, g, rd, wr, hl⟩ => ?_
    rw [hg₁] at hv hf
    refine ⟨fun k hk l hl => ?_, ?_, by rw [g, hg₁], by rw [rd]; simp [s₁], by rw [wr]; simp [s₁],
      fun r' l => by rw [hl]; simp [s₁, State.lane]⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf.readW (r := ⟨s.gpr base + BitVec.ofNat 64 (32 * j + 16 * l), 16⟩) (Region.contains_self _ _)
          (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        show (s.mem.writeW (s.gpr base + BitVec.ofNat 64 (32 * j)) (s.ymm r)).readW _ 128 = _
        rw [show s.gpr base + BitVec.ofNat 64 (32 * j + 16 * l) =
          s.gpr base + BitVec.ofNat 64 (32 * j) + BitVec.ofNat 64 (16 * l) by
            rw [BitVec.add_assoc, BitVec.ofNat_add], State.ymm_eq]
        rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
        · have e := readW_writeW_inside s.mem (s.gpr base + BitVec.ofNat 64 (32 * j))
            (s.lane r 1 ++ s.lane r 0) (k := 0) (n := 16) (by decide) (by decide)
          rw [show 16 * 0 = 0 from rfl]
          exact e.trans (extract_lo _ _)
        · have e := readW_writeW_inside s.mem (s.gpr base + BitVec.ofNat 64 (32 * j))
            (s.lane r 1 ++ s.lane r 0) (k := 16) (n := 16) (by decide) (by decide)
          rw [show 16 * 1 = 16 from rfl, e, extract_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega_arith, hv k (by simpa using hk) l hl]
        simp [s₁, State.lane]
    · refine (Frame.writeW (Frame.refl [⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * (rs.length + 1)⟩] s.mem)
        List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega_arith)).trans
        (hf.sub fun r' hr' => ⟨_, List.mem_cons_self, fun x hx => ?_⟩)
      simp only [List.mem_singleton] at hr'
      subst hr'
      exact (Offset.sub _ (by omega_arith) (by omega_arith)) x hx

/-! ## `Y`, the counter, the increment and the pointers -/

theorem setupC_ok (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupC) s fun s' =>
      s'.lane .xmm2 0 = blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm2 1 = 0 ∧
      (∀ l < 2, s'.lane .xmm14 l = Nat.repeat inc32 l (blockAt s.mem (s.gpr .rdx))) ∧
      (∀ l < 2, s'.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) ∧
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r8 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm2 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hy
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hc
  have m0 := h0 0 (by decide)
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [setupC, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', hc', VBinOp.sse, getLsbD_one8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, trivial, fun l hl => ?_, fun l hl => ?_, ?_, trivial, trivial, fun r h1 h2 h3 => ?_,
    fun r h2 h13 h14 h15 l hl => ?_, trivial, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]
      rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
    · simp only [Nat.one_ne_zero, ite_false]
      rw [BitVec.ofInt_natCast, BitVec.add_zero, ← VG.Proof.Gcm.X86_64.blockAt_eq]
      exact VG.Proof.Aes.X86_64.AesNi.paddd_one _
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · bv_omega
  · simp [h1, h2, h3]
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2, h13, h14, h15]

/-- `vpxor xmm12, xmm12, xmm12`, which clears `ymm12`. -/
theorem zero12_ok (s : State) :
    WP isa (.block [.vop (.vbin .vpxor .l128 .xmm12 .xmm12 .xmm12)]) s fun s' =>
      (∀ l < 2, s'.lane .xmm12 l = 0) ∧ (∀ x, x ≠ .xmm12 → ∀ l < 2, s'.lane x l = s.lane x l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun x h l hl => ?_, rfl, rfl, rfl, rfl⟩
  · have z : ((if l = 0 then 0#128 else 0) : BitVec 128) = 0 := ite_self _
    rw [← State.zlane_lt2 _ _ hl]
    simp only [VOp.exec, State.zlane_setV128 _ _ _ _ _ (show l < 4 by omega_arith), VBinOp.sse, Pclmul.eval_pxor,
      BitVec.xor_self, ite_true, z]
  · rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl]
    simp only [VOp.exec, State.zlane_setV128 _ _ _ _ _ (show l < 4 by omega_arith), h, ite_false]

/-- `zeroPow`: the copy of the powers at `scratch` cleared, which the
postcondition allows. -/
theorem zeroPow_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {s : State} (h : EPost s₀ s) :
    WP isa (.block Impl.Gcm.X86_64.Stitch.zeroPow) s (EPost s₀) := by
  have h11 : s.gpr .r11 = Stitch.pp s₀ := h.gpr _ (by decide) (by decide) (by decide) (by decide)
  have hwp := hp.wrap_p
  rw [show Impl.Gcm.X86_64.Stitch.zeroPow = [.vop (.vbin .vpxor .l128 .xmm12 .xmm12 .xmm12)] ++
    Impl.Gcm.X86_64.Stitch.storesK .r11 (List.replicate 8 .xmm12) 0 from rfl, WP.block_append_iff]
  refine WP.mono (zero12_ok s) fun s₁ ⟨z₁, k₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (Stitch.storesK_ok .r11 (List.replicate 8 .xmm12) 0 s₁ (fun k hk => by
      rw [wr₁, h.wr, g₁, h11]; exact Stitch.in_sub_int hp.p_in (by simp at hk; omega_using [hk]))
    (by rw [g₁, h11]; simp; omega_using [hwp])) fun s₂ ⟨sv, fr, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [g₁, h11, m₁, Nat.mul_zero, BitVec.add_zero, show 32 * (List.replicate 8 XReg.xmm12).length = 256 by simp] at fr
  have F : Frame [Stitch.pR s₀] s.mem s₂.mem := fr.sub fun r hr => ⟨Stitch.pR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  have keep : ∀ p, Region.Disjoint ⟨p, 16⟩ (Stitch.pR s₀) → Spec.Gcm.blockAt s₂.mem p = Spec.Gcm.blockAt s.mem p :=
    fun p hd => VG.Proof.Aes.X86_64.AesNi.blockAt_frame F fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd
  have hbl : Spec.Gcm.blocksAt s₂.mem (Stitch.dp s₀) (nb s₀) = Spec.Gcm.blocksAt s.mem (Stitch.dp s₀) (nb s₀) := by
    simp only [Spec.Gcm.blocksAt]
    exact List.map_congr_left fun k hk => keep _
      (hp.d_p.sub_left (Offset.sub_base _ (by simp at hk; omega_using [hk])))
  exact ⟨by rw [hbl]; exact h.data, by rw [keep _ hp.p_c.symm]; exact h.ctr,
    by rw [keep _ hp.p_y.symm, hbl]; exact h.y,
    h.frame.trans (F.sub fun r hr => ⟨Stitch.pR s₀, by simp, by simp at hr; subst hr; exact fun _ h => h⟩),
    fun q h1 h2 h3 h4 => by rw [g₂, g₁]; exact h.gpr q h1 h2 h3 h4, by rw [rd₂, rd₁]; exact h.rd,
    by rw [wr₂, wr₁]; exact h.wr⟩

/-- `zeroPow` after the decryption: the copy of the powers cleared, which the
postcondition allows. -/
theorem zeroPowD_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {s : State} (h : DPost s₀ s) :
    WP isa (.block Impl.Gcm.X86_64.Stitch.zeroPow) s (DPost s₀) := by
  have h11 : s.gpr .r11 = Stitch.pp s₀ := h.gpr _ (by decide) (by decide) (by decide) (by decide)
  have hwp := hp.wrap_p
  rw [show Impl.Gcm.X86_64.Stitch.zeroPow = [.vop (.vbin .vpxor .l128 .xmm12 .xmm12 .xmm12)] ++
    Impl.Gcm.X86_64.Stitch.storesK .r11 (List.replicate 8 .xmm12) 0 from rfl, WP.block_append_iff]
  refine WP.mono (zero12_ok s) fun s₁ ⟨z₁, k₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (Stitch.storesK_ok .r11 (List.replicate 8 .xmm12) 0 s₁ (fun k hk => by
      rw [wr₁, h.wr, g₁, h11]; exact Stitch.in_sub_int hp.p_in (by simp at hk; omega_using [hk]))
    (by rw [g₁, h11]; simp; omega_using [hwp])) fun s₂ ⟨sv, fr, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [g₁, h11, m₁, Nat.mul_zero, BitVec.add_zero, show 32 * (List.replicate 8 XReg.xmm12).length = 256 by simp] at fr
  have F : Frame [Stitch.pR s₀] s.mem s₂.mem := fr.sub fun r hr => ⟨Stitch.pR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  have keep : ∀ p, Region.Disjoint ⟨p, 16⟩ (Stitch.pR s₀) → Spec.Gcm.blockAt s₂.mem p = Spec.Gcm.blockAt s.mem p :=
    fun p hd => VG.Proof.Aes.X86_64.AesNi.blockAt_frame F fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd
  have hbl : Spec.Gcm.blocksAt s₂.mem (Stitch.dp s₀) (nb s₀) = Spec.Gcm.blocksAt s.mem (Stitch.dp s₀) (nb s₀) := by
    simp only [Spec.Gcm.blocksAt]
    exact List.map_congr_left fun k hk => keep _
      (hp.d_p.sub_left (Offset.sub_base _ (by simp at hk; omega_using [hk])))
  exact ⟨by rw [hbl]; exact h.data, by rw [keep _ hp.p_c.symm]; exact h.ctr,
    by rw [keep _ hp.p_y.symm]; exact h.y,
    h.frame.trans (F.sub fun r hr => ⟨Stitch.pR s₀, by simp, by simp at hr; subst hr; exact fun _ h => h⟩),
    fun q h1 h2 h3 h4 => by rw [g₂, g₁]; exact h.gpr q h1 h2 h3 h4, by rw [rd₂, rd₁]; exact h.rd,
    by rw [wr₂, wr₁]; exact h.wr⟩

end VG.Proof.Gcm.X86_64.Stitch
