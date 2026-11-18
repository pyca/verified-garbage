module

import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Load
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZR
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Gcm.X86_64.Prepared.Loop`, which the modules that import this one used -/

section

/-! ### `Gcm.X86_64.StitchZ.LoopP`, which this module and modules that import it used -/

section

/-!
# The AVX-512 loops, with the powers in the key context

Untrusted: everything here is checked by Lean. `powP48_ok`: `StitchZP.powP48`
stores the tables of `StitchZ.pow48`, each pair converted from the powers in
the key context (`cvtPair_ok`, stored by `Stitch.storesK_ok`), which the
working space, written so far, is apart from (`kblk`, `SPreP.p_k`).
`bigP_ok`, `bigDP_ok`: `StitchZ.bigRest_ok` and `bigDRest_ok` after them, for
the tables whose last is the setup's powers (`setupP_ok`) and the others
those `powP48` stores. `encTailP_ok` and `decTailP_ok` are `StitchZ`'s tails
with these.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZP

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreP kPR kp pp hk dp nb pR dR in_sub_int in_sub in_rdwr storesK_ok)
open VG.Proof.Gcm.X86_64.StitchZ (EInv DInv AInv FinOk FinOk48 bigRest_ok bigDRest_ok AInv.pow)
open VG.Proof.Gcm.X86_64.Pclmul (ea_at)
open VG.Proof.Gcm.X86_64.StitchZ (readW_lane)
open VG.Proof.Aes.X86_64.VaesZ (zmm_lane)
open VG.Impl.Gcm.X86_64.Pclmul (at_ xInv poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK)
open VG.Impl.Gcm.X86_64.StitchZ (tab)
open VG.Impl.Gcm.X86_64.StitchZP (cvtConsts cvtPair hInvY powPair powP48 bigP bigDP)
open VG.Spec.Gcm (Block blockAt)

/-! ## Helpers -/

/-- Two things a block does, from one run. -/
theorem WP.block_and {is : List Instr} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa (.block is) s Q₁)
    (h₂ : WP isa (.block is) s Q₂) : WP isa (.block is) s fun s' => Q₁ s' ∧ Q₂ s' := by
  obtain ⟨s₁, e₁, q₁⟩ := WP.runBlock_of h₁
  obtain ⟨s₂, e₂, q₂⟩ := WP.runBlock_of h₂
  rw [e₁, Option.some.injEq] at e₂
  subst e₂
  exact WP.of_runBlock ⟨s₁, e₁, q₁, q₂⟩

/-- A block of the key context is kept by writes to the working space. -/
theorem kblk {s₀ : State} (hp : SPreP s₀) {m m' : Mem} (hf : Frame [pR s₀] m m') {o : Nat} (ho : o + 16 ≤ 1024) :
    blockAt m' (kp s₀ + BitVec.ofNat 64 o) = blockAt m (kp s₀ + BitVec.ofNat 64 o) :=
  VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := hp.wrap_k
    exact hp.p_k.symm.sub_left (Offset.sub_base _ ho)

/-- The powers of the key context are kept by writes to the working space. -/
theorem pow_frame {s₀ : State} (hp : SPreP s₀) {m m' : Mem} (hf : Frame [pR s₀] m m')
    (h : Spec.Gcm.PowersRepr m (kp s₀)) : Spec.Gcm.PowersRepr m' (kp s₀) ∧ Spec.Gcm.ctxH m' (kp s₀) = Spec.Gcm.ctxH m (kp s₀) := by
  have hH : Spec.Gcm.ctxH m' (kp s₀) = Spec.Gcm.ctxH m (kp s₀) := kblk hp hf (o := 240) (by decide)
  exact ⟨fun k hk => by rw [kblk hp hf (by omega_arith), h k hk, hH], hH⟩

/-- A 128-bit load into `d`, which only `d` changes. -/
theorem ld128_ok (d : XReg) (b : Reg) (o : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (o : Int)) 16) :
    WP isa (.block [.vmovdquLoad .l128 d (at_ b o)]) s fun s' => ZFrame [d] s s' := by
  rw [WP.block_cons_iff]
  refine ⟨s.setV .l128 d (s.mem.readW (s.gpr b + BitVec.ofInt 64 (o : Int)) 128) 0,
    by simp only [isa, exec, State.load128, ea_at, hin, ite_true, Option.map_some],
    WP.block_nil ⟨rfl, rfl, rfl, rfl, fun r hr l _ => ?_⟩⟩
  exact State.zlane_setV_ne _ _ (fun h => hr (List.mem_singleton.mpr h)) _ _ _

/-- `cvtPair j xmm12`, as `cvtPair_ok` says, and only `ymm7`, `ymm10` and
`ymm12` change. -/
theorem cvt12_ok (j : Nat) (s : State) (m0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (c8 : ∀ l < 2, s.lane .xmm8 l = xInv) (c9 : ∀ l < 2, s.lane .xmm9 l = ones)
    (hin₀ : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((256 + 16 * j : Nat) : Int)) 16)
    (hin₁ : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((240 + 16 * j : Nat) : Int)) 16) :
    WP isa (.block (cvtPair j .xmm12)) s fun s' =>
      (s'.lane .xmm12 0 = hInvF (blockAt s.mem (s.gpr .rdi + BitVec.ofInt 64 ((256 + 16 * j : Nat) : Int))) ∧
        s'.lane .xmm12 1 = hInvF (blockAt s.mem (s.gpr .rdi + BitVec.ofInt 64 ((240 + 16 * j : Nat) : Int))) ∧
        YFrame [.xmm7, .xmm10, .xmm12] s s') ∧ ZFrame [.xmm7, .xmm10, .xmm12] s s' := by
  refine WP.block_and (cvtPair_ok j .xmm12 (by decide) (by decide) (by decide) (by decide) s m0 c8 c9 hin₀ hin₁) ?_
  rw [cvtPair, show ([.vmovdquLoad .l128 .xmm7 (at_ .rdi (256 + 16 * j)), .vmovdquLoad .l128 .xmm10 (at_ .rdi (240 + 16 * j)),
      .vop (.vinserti128 .xmm7 .xmm7 .xmm10 1), .vop (.vbin .vpshufb .l256 .xmm7 .xmm7 .xmm0)] : List Instr) =
      [.vmovdquLoad .l128 .xmm7 (at_ .rdi (256 + 16 * j))] ++ ([.vmovdquLoad .l128 .xmm10 (at_ .rdi (240 + 16 * j))] ++
      [.vop (.vinserti128 .xmm7 .xmm7 .xmm10 1), .vop (.vbin .vpshufb .l256 .xmm7 .xmm7 .xmm0)]) from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (ld128_ok .xmm7 .rdi _ s hin₀) fun s₁ f₁ => ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ld128_ok .xmm10 .rdi _ s₁ (by rw [f₁.rd, f₁.wr, f₁.gpr]; exact hin₁)) fun s₂ f₂ => ?_
  obtain ⟨s₃, e₃, -⟩ := zframe_block [.xmm7, .xmm10, .xmm12]
    ([.vop (.vinserti128 .xmm7 .xmm7 .xmm10 1), .vop (.vbin .vpshufb .l256 .xmm7 .xmm7 .xmm0)] ++
      hInvY .xmm12 .xmm7 .xmm10) (by decide) s₂
  refine WP.mono (WP.zframe (by decide) (Q := fun _ => True) (WP.of_runBlock ⟨s₃, e₃, trivial⟩))
    fun s' ⟨_, f'⟩ => ((f₁.mono (by decide)).trans ((f₂.mono (by decide)).trans f'))

/-- A word outside a region written is kept. -/
theorem keepAt {p : Addr} {m m' : Mem} {o len : Nat} (f : Frame [⟨p + BitVec.ofNat 64 o, len⟩] m m') {a : Nat}
    (ha : a + 16 ≤ o ∨ o + len ≤ a) (hl : o + len ≤ 2 ^ 64) (hal : a + 16 ≤ 2 ^ 64) :
    m'.readW (p + BitVec.ofNat 64 a) 128 = m.readW (p + BitVec.ofNat 64 a) 128 :=
  f.readW (r := ⟨p + BitVec.ofNat 64 a, 16⟩) (Region.contains_self _ _)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ ha hal hl) (by decide)

/-- The power of the key context at `256 + 16 k`. -/
theorem powm {m : Mem} {p : Addr} (h : Spec.Gcm.PowersRepr m p) {k : Nat} (hk : k < 48) :
    blockAt m (p + BitVec.ofInt 64 ((256 + 16 * k : Nat) : Int)) = Spec.Gcm.hpow (Spec.Gcm.ctxH m p) (k + 1) := by
  rw [BitVec.ofInt_natCast, h k hk]

/-- A 256-bit store keeps the registers. -/
theorem st_zlane (b : Reg) (r : XReg) (j : Nat) (s : State)
    (hin : InRegions s.wr (s.gpr b + BitVec.ofInt 64 ((32 * j : Nat) : Int)) 32) :
    WP isa (.block (storesK b [r] j)) s fun s' => ∀ r' l, s'.zlane r' l = s.zlane r' l := by
  simp only [storesK]
  rw [WP.block_cons_iff]
  exact ⟨s.setMem (s.mem.writeW (s.gpr b + BitVec.ofInt 64 ((32 * j : Nat) : Int)) (s.ymm r)),
    by simp only [isa, exec, State.store256_eq, ea_at, hin, ite_true], WP.block_nil fun _ _ => rfl⟩

/-- What the conversions of a table need. -/
structure CvtEnv (s₀ : State) (s : State) : Prop where
  rdi : s.gpr .rdi = kp s₀
  r11 : s.gpr .r11 = pp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pow : Spec.Gcm.PowersRepr s.mem (kp s₀)
  m0 : ∀ l < 2, s.lane .xmm0 l = revMask
  c8 : ∀ l < 2, s.lane .xmm8 l = xInv
  c9 : ∀ l < 2, s.lane .xmm9 l = ones

/-- Pair `m` of table `g`. -/
theorem powPair_ok {s₀ : State} (hp : SPreP s₀) {g m : Nat} (hg : g < 2) (hm : m < 8) {s : State} (E : CvtEnv s₀ s) :
    WP isa (.block (powPair g m)) s fun s' =>
      (∀ l < 2, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 32 * m + 16 * l)) 128 =
        hInvF (Spec.Gcm.hpow (Spec.Gcm.ctxH s.mem (kp s₀)) (48 - 16 * g - 2 * m - l))) ∧
      Frame [⟨pp s₀ + BitVec.ofNat 64 (tab g + 32 * m), 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ r, r ≠ .xmm7 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  have hwp := hp.base.wrap_p
  have kin : ∀ o : Nat, o + 16 ≤ 1024 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 (o : Int)) 16 :=
    fun o ho => by rw [E.rd, E.wr, E.rdi]; exact in_sub_int hp.k_in ho
  rw [powPair, WP.block_append_iff]
  refine WP.mono (cvt12_ok (48 - 16 * g - 2 * m - 1) s E.m0 E.c8 E.c9 (kin _ (by omega_arith)) (kin _ (by omega_arith)))
    fun s₁ ⟨⟨v0, v1, _⟩, z₁⟩ => ?_
  have j32 : 32 * (16 - 8 * g + m) = tab g + 32 * m := by simp only [tab]; omega_arith
  have hin : ∀ k < [XReg.xmm12].length, InRegions s₁.wr (s₁.gpr .r11 + BitVec.ofInt 64 ((32 * (16 - 8 * g + m + k) : Nat) : Int)) 32 :=
    fun k hk => by
      simp only [List.length_singleton] at hk
      rw [z₁.wr, z₁.gpr, E.wr, E.r11]; exact in_sub_int hp.base.p_in (by simp only [tab] at j32; omega_arith)
  refine WP.mono (WP.block_and (storesK_ok .r11 [.xmm12] _ s₁ hin
      (by rw [z₁.gpr, E.r11]; simp only [tab] at j32; simp; omega_arith))
      (st_zlane .r11 .xmm12 _ s₁ (by simpa using hin 0 (by simp))))
    fun s' ⟨⟨sv, fr, g', rd', wr', _⟩, hz⟩ => ?_
  rw [z₁.gpr, E.r11] at sv fr
  rw [z₁.mem] at fr
  simp only [List.length_singleton, Nat.mul_one, j32] at fr
  refine ⟨fun l hl => ?_, fr, by rw [g', z₁.gpr], by rw [rd', z₁.rd], by rw [wr', z₁.wr],
    fun r h7 h10 h12 l hl => by rw [hz, z₁.zlane r (by simp [h7, h10, h12]) l hl]⟩
  have e := sv 0 (by simp) l hl
  rw [Nat.add_zero, j32] at e
  rw [e]
  simp only [List.getElem_cons_zero]
  rw [E.rdi] at v0 v1
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
  · rw [v0, powm E.pow (by omega_arith)]; congr 2; omega_arith
  · rw [v1, show 240 + 16 * (48 - 16 * g - 2 * m - 1) = 256 + 16 * (48 - 16 * g - 2 * m - 2) by omega_arith,
      powm E.pow (by omega_arith)]; congr 2; omega_arith

/-- A frame of a part of a region is one of the region. -/
theorem frame_sub {p : Addr} {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) {m m' : Mem}
    (f : Frame [⟨p + BitVec.ofNat 64 d, n⟩] m m') : Frame [⟨p + BitVec.ofNat 64 e, k⟩] m m' :=
  f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub p h₁ h₂⟩

theorem frame_pR {s₀ : State} {e k : Nat} (h : e + k ≤ 1024) {m m' : Mem}
    (f : Frame [⟨pp s₀ + BitVec.ofNat 64 e, k⟩] m m') : Frame [pR s₀] m m' :=
  f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ h⟩

/-- The first `n` pairs of table `g`. -/
theorem powRun_ok {s₀ : State} (hp : SPreP s₀) {g : Nat} (hg : g < 2) :
    ∀ n, n ≤ 8 → ∀ s, CvtEnv s₀ s →
      WP isa (.block ((List.range n).flatMap (powPair g))) s fun s' =>
        (∀ m < n, ∀ l < 2, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 32 * m + 16 * l)) 128 =
          hInvF (Spec.Gcm.hpow (Spec.Gcm.ctxH s.mem (kp s₀)) (48 - 16 * g - 2 * m - l))) ∧
        Frame [⟨pp s₀ + BitVec.ofNat 64 (tab g), 32 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ (∀ r, r ≠ .xmm7 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 4, s'.zlane r l = s.zlane r l)
  | 0, _, s, _ => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨fun m hm => absurd hm (by omega_arith), Frame.refl _ _, rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl⟩
  | n + 1, hn, s, E => by
    have hwp := hp.base.wrap_p
    have htab : tab g ≤ 512 := by simp only [tab]; omega_arith
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (powRun_ok hp hg n (by omega_arith) s E) fun s₁ ⟨p₁, f₁, g₁, rd₁, wr₁, z₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨pw₁, hH₁⟩ := pow_frame hp (frame_pR (by omega_arith) f₁) E.pow
    have lk : ∀ r ∈ ([.xmm0, .xmm8, .xmm9] : List XReg), ∀ l < 2, s₁.lane r l = s.lane r l := fun r hr l hl => by
      rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact z₁ _ (by decide) (by decide) (by decide) l (by omega_arith)
    have E₁ : CvtEnv s₀ s₁ := ⟨by rw [g₁]; exact E.rdi, by rw [g₁]; exact E.r11, by rw [rd₁]; exact E.rd,
      by rw [wr₁]; exact E.wr, pw₁, fun l hl => by rw [lk _ (by simp) l hl]; exact E.m0 l hl,
      fun l hl => by rw [lk _ (by simp) l hl]; exact E.c8 l hl, fun l hl => by rw [lk _ (by simp) l hl]; exact E.c9 l hl⟩
    refine WP.mono (powPair_ok hp hg (by omega_arith : n < 8) E₁) fun s' ⟨v, f', g', rd', wr', z'⟩ => ⟨fun m hm l hl => ?_,
      (frame_sub (Nat.le_refl _) (by omega_arith) f₁).trans (frame_sub (by omega_arith) (by omega_arith) f'),
      by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁],
      fun r h7 h10 h12 l hl => by rw [z' r h7 h10 h12 l hl, z₁ r h7 h10 h12 l hl]⟩
    by_cases hmn : m = n
    · subst hmn; rw [v l hl, hH₁]
    · rw [keepAt f' (by omega_arith) (by omega_arith) (by omega_arith)]; exact p₁ m (by omega_arith) l hl

/-- `powP48`: the tables `g = 1` (`H'³²`–`H'¹⁷`) and `g = 0` (`H'⁴⁸`–`H'³³`)
from the powers of the key context, and the reduction constant at
`scratch + 832`. -/
theorem powP48_ok {s₀ : State} (hp : SPreP s₀) {s : State} (hdi : s.gpr .rdi = kp s₀) (hr11 : s.gpr .r11 = pp s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hpw : Spec.Gcm.PowersRepr s.mem (kp s₀))
    (m0 : ∀ l < 2, s.lane .xmm0 l = revMask) (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) :
    WP isa (.block powP48) s fun s' =>
      (∀ g < 2, ∀ k < 4, ∀ l < 4, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 =
        hInvF (Spec.Gcm.hpow (Spec.Gcm.ctxH s.mem (kp s₀)) (48 - 16 * g - 4 * k - l))) ∧
      (∀ l < 4, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) ∧
      (∀ o, o + 16 ≤ 256 → s'.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 = s.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128) ∧
      Frame [pR s₀] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  have hwp := hp.base.wrap_p
  rw [powP48, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.block_and (consts_ok s fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact h1 l (by omega_arith))
    (WP.zframe (rs := [.xmm8, .xmm9]) (by decide) (Q := fun _ => True)
      (WP.of_runBlock ⟨_, (zframe_block [.xmm8, .xmm9] cvtConsts (by decide) s).choose_spec.1, trivial⟩)))
    fun s₁ ⟨⟨c8, c9, _⟩, _, z₁⟩ => ?_
  have l₁ : ∀ r, r ≠ .xmm8 → r ≠ .xmm9 → ∀ l < 4, s₁.zlane r l = s.zlane r l :=
    fun r h8 h9 l hl => z₁.zlane r (by simp [h8, h9]) l hl
  have m0₁ : ∀ l < 2, s₁.lane .xmm0 l = revMask := fun l hl => by
    rw [← State.zlane_lt2 _ _ hl, l₁ _ (by decide) (by decide) l (by omega_arith), State.zlane_lt2 _ _ hl]; exact m0 l hl
  have E₁ : CvtEnv s₀ s₁ := ⟨by rw [z₁.gpr]; exact hdi, by rw [z₁.gpr]; exact hr11, by rw [z₁.rd]; exact hrd,
    by rw [z₁.wr]; exact hwr, by rw [z₁.mem]; exact hpw, m0₁, c8, c9⟩
  rw [WP.block_append_iff]
  refine WP.mono (powRun_ok hp (g := 1) (by decide) 8 (Nat.le_refl _) s₁ E₁) fun s₂ ⟨t₂, f₂, g₂, rd₂, wr₂, z₂⟩ => ?_
  obtain ⟨pw₂, hH₂⟩ := pow_frame hp (frame_pR (by simp only [tab]; omega_arith) f₂) E₁.pow
  have lk : ∀ r ∈ ([.xmm0, .xmm8, .xmm9] : List XReg), ∀ l < 2, s₂.lane r l = s₁.lane r l := fun r hr l hl => by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact z₂ _ (by decide) (by decide) (by decide) l (by omega_arith)
  have E₂ : CvtEnv s₀ s₂ := ⟨by rw [g₂]; exact E₁.rdi, by rw [g₂]; exact E₁.r11, by rw [rd₂]; exact E₁.rd,
    by rw [wr₂]; exact E₁.wr, pw₂, fun l hl => by rw [lk _ (by simp) l hl]; exact E₁.m0 l hl,
    fun l hl => by rw [lk _ (by simp) l hl]; exact E₁.c8 l hl, fun l hl => by rw [lk _ (by simp) l hl]; exact E₁.c9 l hl⟩
  rw [WP.block_append_iff]
  refine WP.mono (powRun_ok hp (g := 0) (by decide) 8 (Nat.le_refl _) s₂ E₂) fun s₃ ⟨t₃, f₃, g₃, rd₃, wr₃, z₃⟩ => ?_
  -- The reduction constant, stored.
  have g₃' : s₃.gpr = s.gpr := by rw [g₃, g₂, z₁.gpr]
  have e832 : s₃.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int) = pp s₀ + BitVec.ofNat 64 832 := by
    rw [g₃', hr11, BitVec.ofInt_natCast]
  have hin832 : InRegions s₃.wr (s₃.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)) 64 := by
    rw [wr₃, wr₂, z₁.wr, hwr, e832]; exact in_sub hp.base.p_in (by decide)
  rw [WP.block_cons_iff]
  refine ⟨s₃.setMem (s₃.mem.writeW (pp s₀ + BitVec.ofNat 64 832) (s₃.zmm .xmm1)),
    by simp only [isa, exec, State.store512_eq, ea_at, hin832, ite_true]; rw [e832], WP.block_nil ?_⟩
  have k₅ : ∀ o, o + 16 ≤ 832 → (s₃.mem.writeW (pp s₀ + BitVec.ofNat 64 832) (s₃.zmm .xmm1)).readW
      (pp s₀ + BitVec.ofNat 64 o) 128 = s₃.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 := fun o ho =>
    Mem.readW_writeW_sep (Offset.sep (pp s₀) (d := o) (n := 128 / 8) (e := 832) (k := 512 / 8) (by omega_arith) (by omega_arith)
      (by omega_arith)) (by decide)
  have z13 : ∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 4, s₃.zlane r l = s.zlane r l :=
    fun r h7 h8 h9 h10 h12 l hl => by rw [z₃ r h7 h10 h12 l hl, z₂ r h7 h10 h12 l hl, l₁ r h8 h9 l hl]
  refine ⟨fun g hg k hk l hl => ?_, fun l hl => ?_, fun o ho => ?_, ?_, by rw [State.setMem_gpr, g₃'],
    by rw [State.setMem_rd, rd₃, rd₂, z₁.rd], by rw [State.setMem_wr, wr₃, wr₂, z₁.wr],
    fun r h7 h8 h9 h10 h12 l hl => by rw [State.setMem_zlane, z13 r h7 h8 h9 h10 h12 l hl]⟩
  · rw [State.setMem_mem, k₅ _ (by simp only [tab]; omega_arith),
      show tab g + 64 * k + 16 * l = tab g + 32 * (2 * k + l / 2) + 16 * (l % 2) by omega_arith]
    rcases (by omega_arith : g = 0 ∨ g = 1) with rfl | rfl
    · rw [t₃ _ (by omega_arith) _ (by omega_arith), hH₂, z₁.mem]; congr 2; omega_arith
    · rw [keepAt f₃ (by simp only [tab]; omega_arith) (by simp only [tab]; omega_arith) (by simp only [tab]; omega_arith),
        t₂ _ (by omega_arith) _ (by omega_arith), z₁.mem]; congr 2; omega_arith
  · rw [State.setMem_mem, show pp s₀ + BitVec.ofNat 64 (832 + 16 * l) = pp s₀ + BitVec.ofNat 64 832 + BitVec.ofNat 64 (16 * l) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add], readW_lane _ _ _ hl, zmm_lane _ _ hl,
      z13 _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl]
    exact h1 l hl
  · rw [State.setMem_mem, k₅ _ (by omega_arith), keepAt f₃ (by simp only [tab]; omega_arith) (by simp only [tab]; omega_arith) (by omega_arith),
      keepAt f₂ (by simp only [tab]; omega_arith) (by simp only [tab]; omega_arith) (by omega_arith), z₁.mem]
  · rw [State.setMem_mem, ← z₁.mem]
    exact ((frame_pR (by simp only [tab]; omega_arith) f₂).trans (frame_pR (by simp only [tab]; omega_arith) f₃)).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

/-! ## From 256 blocks on -/

/-- The key context, with its powers, is kept by the loops, which write only
the data and the working space. -/
theorem ctx_keep {s₀ : State} (hp : SPreP s₀) {m : Mem} (hf : Frame [dR s₀, pR s₀] s₀.mem m) :
    Spec.Gcm.PowersRepr m (kp s₀) ∧ Spec.Gcm.ctxH m (kp s₀) = hk s₀ := by
  have hwk := hp.wrap_k
  have kb : ∀ o, o + 16 ≤ 1024 → blockAt m (kp s₀ + BitVec.ofNat 64 o) = blockAt s₀.mem (kp s₀ + BitVec.ofNat 64 o) :=
    fun o ho => VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.d_k.symm.sub_left (Offset.sub_base _ ho)
      · exact hp.p_k.symm.sub_left (Offset.sub_base _ ho)
  have hH : Spec.Gcm.ctxH m (kp s₀) = hk s₀ := kb 240 (by decide)
  refine ⟨fun k hk => ?_, hH⟩
  rw [kb _ (by omega_arith), hp.pow k hk, hH]; rfl

/-- `bigP`: `big` with the tables loaded. -/
theorem bigP_ok {s₀ : State} (hp : SPreP s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) (h96 : 96 ≤ nb s₀) {s : State}
    (hI : EInv s₀ P 1 s) : WP isa bigP s fun s' => ∃ e, EInv s₀ P e s' := by
  have hdi : s.gpr .rdi = kp s₀ := hI.gpr .rdi (by decide) (by decide) (by decide) (by decide)
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hpw, hH⟩ := ctx_keep hp hI.a.frame
  refine WP.seq (WP.mono (powP48_ok hp hdi hr11 hI.a.rd hI.a.wr hpw
    (fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact hI.a.msk l (by omega_arith)) hI.m1)
    fun s₁ ⟨t, pm, keep, fr, g₁, rd₁, wr₁, z₁⟩ => ?_)
  rw [hH] at t
  let T : Nat → Nat → Nat → Block := fun g k l =>
    if g = 2 then P k l else s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128
  have hv : ∀ g < 3, ∀ k < 4, ∀ l < 4,
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l := fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2
      simp only [T, ↓reduceIte, show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega_arith]
      rw [keep _ (by omega_arith)]; exact hI.pw k hk l hl
    · simp only [T, h2, ↓reduceIte]
  have hT : FinOk48 (hk s₀) T := hFin T fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2; simp only [T, ↓reduceIte]; rw [hP k hk l hl]
    · simp only [T, h2, ↓reduceIte]; exact t g (by omega_arith) k hk l hl
  exact bigRest_ok hp.base hf hT (fun k l => by simp only [T, ↓reduceIte]) h96 hI
    (hI.a.pow hp.base fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl) hv pm g₁
    fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl

/-- `bigDP`: `bigD` with the tables loaded. -/
theorem bigDP_ok {s₀ : State} (hp : SPreP s₀) {P : Nat → Nat → Block}
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) (h96 : 96 ≤ nb s₀) {s : State}
    (hI : DInv s₀ P 0 s) : WP isa bigDP s fun s' => ∃ e, DInv s₀ P e s' := by
  have hdi : s.gpr .rdi = kp s₀ := hI.gpr .rdi (by decide) (by decide) (by decide) (by decide)
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hpw, hH⟩ := ctx_keep hp hI.a.frame
  refine WP.seq (WP.mono (powP48_ok hp hdi hr11 hI.a.rd hI.a.wr hpw
    (fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact hI.a.msk l (by omega_arith)) hI.m1)
    fun s₁ ⟨t, pm, keep, fr, g₁, rd₁, wr₁, z₁⟩ => ?_)
  rw [hH] at t
  let T : Nat → Nat → Nat → Block := fun g k l =>
    if g = 2 then P k l else s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128
  have hv : ∀ g < 3, ∀ k < 4, ∀ l < 4,
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l := fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2
      simp only [T, ↓reduceIte, show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega_arith]
      rw [keep _ (by omega_arith)]; exact hI.pw k hk l hl
    · simp only [T, h2, ↓reduceIte]
  have hT : FinOk48 (hk s₀) T := hFin T fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2; simp only [T, ↓reduceIte]; rw [hP k hk l hl]
    · simp only [T, h2, ↓reduceIte]; exact t g (by omega_arith) k hk l hl
  exact bigDRest_ok hp.base hT (fun k l => by simp only [T, ↓reduceIte]) h96 hI
    (hI.a.pow hp.base fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl) hv pm g₁
    fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl

end VG.Proof.Gcm.X86_64.StitchZP

end

end

/-! # Loading the larger GHASH tables from a prepared context -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZR
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPrePrepared CtxMode kp pp hk nb pR dR in_sub_int in_sub storesK_ok)
open VG.Proof.Gcm.X86_64.StitchZ (EInv DInv FinOk FinOk48 bigRest_ok bigDRest_ok AInv.pow readW_lane)
open VG.Proof.Gcm.X86_64.Pclmul (ea_at)
open VG.Proof.Aes.X86_64.VaesZ (zmm_lane)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchZ (tab)
open VG.Impl.Gcm.X86_64.StitchZR (powPair powP48 bigP bigDP)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF WP.block_and keepAt st_zlane frame_sub frame_pR)
open VG.Spec.Gcm (Block blockAt)

/-- A block of the key context is kept by writes to the working space. -/
theorem kblk {s₀ : State} (hp : SPrePrepared s₀) {m m' : Mem} (hf : Frame [pR s₀] m m') {o : Nat} (ho : o + 16 ≤ 1024) :
    blockAt m' (kp s₀ + BitVec.ofNat 64 o) = blockAt m (kp s₀ + BitVec.ofNat 64 o) :=
  VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := hp.wrap_k
    exact hp.p_k.symm.sub_left (Offset.sub_base _ ho)

/-- The powers of the key context are kept by writes to the working space. -/
theorem pow_frame {s₀ : State} (hp : SPrePrepared s₀) {m m' : Mem} (hf : Frame [pR s₀] m m')
    (h : Spec.Gcm.PreparedPowersRepr m (kp s₀)) : Spec.Gcm.PreparedPowersRepr m' (kp s₀) ∧ Spec.Gcm.ctxH m' (kp s₀) = Spec.Gcm.ctxH m (kp s₀) := by
  have hH : Spec.Gcm.ctxH m' (kp s₀) = Spec.Gcm.ctxH m (kp s₀) := kblk hp hf (o := 240) (by decide)
  exact ⟨CtxMode.prepared.frame hf
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hp.p_k.symm)
    hp.wrap_k h, hH⟩

/-- The addresses, regions and prepared context needed by a pair load. -/
structure CvtEnv (s₀ : State) (s : State) : Prop where
  rdi : s.gpr .rdi = kp s₀
  r11 : s.gpr .r11 = pp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pow : Spec.Gcm.PreparedPowersRepr s.mem (kp s₀)

/-- Pair `m` of table `g`. -/
theorem powPair_ok {s₀ : State} (hp : SPrePrepared s₀) {g m : Nat} (hg : g < 2) (hm : m < 8) {s : State} (E : CvtEnv s₀ s) :
    WP isa (.block (powPair g m)) s fun s' =>
      (∀ l < 2, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 32 * m + 16 * l)) 128 =
        hInvF (Spec.Gcm.hpow (Spec.Gcm.ctxH s.mem (kp s₀)) (48 - 16 * g - 2 * m - l))) ∧
      Frame [⟨pp s₀ + BitVec.ofNat 64 (tab g + 32 * m), 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ r, r ≠ .xmm7 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  have hwp := hp.base.wrap_p
  have kin : ∀ o : Nat, o + 32 ≤ 1024 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 (o : Int)) 32 :=
    fun o ho => by rw [E.rd, E.wr, E.rdi]; exact in_sub_int hp.k_in ho
  rw [powPair, WP.block_append_iff]
  refine WP.mono (loadPair_ok (48 - 16*g - 2*m - 1) .xmm12 s (kin _ (by omega_arith)))
    fun s₁ ⟨v, z₁⟩ => ?_
  have j32 : 32 * (16 - 8 * g + m) = tab g + 32 * m := by simp only [tab]; omega_arith
  have hin : ∀ k < [XReg.xmm12].length, InRegions s₁.wr (s₁.gpr .r11 + BitVec.ofInt 64 ((32 * (16 - 8 * g + m + k) : Nat) : Int)) 32 :=
    fun k hk => by
      simp only [List.length_singleton] at hk
      rw [z₁.wr, z₁.gpr, E.wr, E.r11]; exact in_sub_int hp.base.p_in (by simp only [tab] at j32; omega_arith)
  refine WP.mono (WP.block_and (storesK_ok .r11 [.xmm12] _ s₁ hin
      (by rw [z₁.gpr, E.r11]; simp only [tab] at j32; simp; omega_arith))
      (st_zlane .r11 .xmm12 _ s₁ (by simpa using hin 0 (by simp))))
    fun s' ⟨⟨sv, fr, g', rd', wr', _⟩, hz⟩ => ?_
  rw [z₁.gpr, E.r11] at sv fr
  rw [z₁.mem] at fr
  simp only [List.length_singleton, Nat.mul_one, j32] at fr
  refine ⟨fun l hl => ?_, fr, by rw [g', z₁.gpr], by rw [rd', z₁.rd], by rw [wr', z₁.wr],
    fun r h7 h10 h12 l hl => by rw [hz, z₁.zlane r (by simp only [List.mem_singleton, h12, not_false_eq_true]) l hl]⟩
  have e := sv 0 (by simp) l hl
  rw [Nat.add_zero, j32] at e
  rw [e]
  simp only [List.getElem_cons_zero]
  rw [v l hl, E.rdi, pair_values E.pow (by omega_arith) (by omega_arith) hl]
  congr 2; omega_arith

/-- The first `n` pairs of table `g`. -/
theorem powRun_ok {s₀ : State} (hp : SPrePrepared s₀) {g : Nat} (hg : g < 2) :
    ∀ n, n ≤ 8 → ∀ s, CvtEnv s₀ s →
      WP isa (.block ((List.range n).flatMap (powPair g))) s fun s' =>
        (∀ m < n, ∀ l < 2, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 32 * m + 16 * l)) 128 =
          hInvF (Spec.Gcm.hpow (Spec.Gcm.ctxH s.mem (kp s₀)) (48 - 16 * g - 2 * m - l))) ∧
        Frame [⟨pp s₀ + BitVec.ofNat 64 (tab g), 32 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ (∀ r, r ≠ .xmm7 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 4, s'.zlane r l = s.zlane r l)
  | 0, _, s, _ => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨fun m hm => absurd hm (by omega_arith), Frame.refl _ _, rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl⟩
  | n + 1, hn, s, E => by
    have hwp := hp.base.wrap_p
    have htab : tab g ≤ 512 := by simp only [tab]; omega_arith
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (powRun_ok hp hg n (by omega_arith) s E) fun s₁ ⟨p₁, f₁, g₁, rd₁, wr₁, z₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨pw₁, hH₁⟩ := pow_frame hp (frame_pR (by omega_arith) f₁) E.pow
    have E₁ : CvtEnv s₀ s₁ := ⟨by rw [g₁]; exact E.rdi, by rw [g₁]; exact E.r11,
      by rw [rd₁]; exact E.rd, by rw [wr₁]; exact E.wr, pw₁⟩
    refine WP.mono (powPair_ok hp hg (by omega_arith : n < 8) E₁) fun s' ⟨v, f', g', rd', wr', z'⟩ => ⟨fun m hm l hl => ?_,
      (frame_sub (Nat.le_refl _) (by omega_arith) f₁).trans (frame_sub (by omega_arith) (by omega_arith) f'),
      by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁],
      fun r h7 h10 h12 l hl => by rw [z' r h7 h10 h12 l hl, z₁ r h7 h10 h12 l hl]⟩
    by_cases hmn : m = n
    · subst hmn; rw [v l hl, hH₁]
    · rw [keepAt f' (by omega_arith) (by omega_arith) (by omega_arith)]; exact p₁ m (by omega_arith) l hl

/-- `powP48`: the tables `g = 1` (`H'³²`–`H'¹⁷`) and `g = 0` (`H'⁴⁸`–`H'³³`)
from the powers of the key context, and the reduction constant at
`scratch + 832`. -/
theorem powP48_ok {s₀ : State} (hp : SPrePrepared s₀) {s : State} (hdi : s.gpr .rdi = kp s₀) (hr11 : s.gpr .r11 = pp s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hpw : Spec.Gcm.PreparedPowersRepr s.mem (kp s₀))
    (_m0 : ∀ l < 2, s.lane .xmm0 l = revMask) (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) :
    WP isa (.block powP48) s fun s' =>
      (∀ g < 2, ∀ k < 4, ∀ l < 4, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 =
        hInvF (Spec.Gcm.hpow (Spec.Gcm.ctxH s.mem (kp s₀)) (48 - 16 * g - 4 * k - l))) ∧
      (∀ l < 4, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) ∧
      (∀ o, o + 16 ≤ 256 → s'.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 = s.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128) ∧
      Frame [pR s₀] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  have hwp := hp.base.wrap_p
  rw [powP48, List.append_assoc, WP.block_append_iff]
  have E₁ : CvtEnv s₀ s := ⟨hdi, hr11, hrd, hwr, hpw⟩
  refine WP.mono (powRun_ok hp (g := 1) (by decide) 8 (Nat.le_refl _) s E₁) fun s₂ ⟨t₂, f₂, g₂, rd₂, wr₂, z₂⟩ => ?_
  obtain ⟨pw₂, hH₂⟩ := pow_frame hp (frame_pR (by simp only [tab]; omega_arith) f₂) E₁.pow
  have E₂ : CvtEnv s₀ s₂ := ⟨by rw [g₂]; exact E₁.rdi, by rw [g₂]; exact E₁.r11,
    by rw [rd₂]; exact E₁.rd, by rw [wr₂]; exact E₁.wr, pw₂⟩
  rw [WP.block_append_iff]
  refine WP.mono (powRun_ok hp (g := 0) (by decide) 8 (Nat.le_refl _) s₂ E₂) fun s₃ ⟨t₃, f₃, g₃, rd₃, wr₃, z₃⟩ => ?_
  -- The reduction constant, stored.
  have g₃' : s₃.gpr = s.gpr := by rw [g₃, g₂]
  have e832 : s₃.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int) = pp s₀ + BitVec.ofNat 64 832 := by
    rw [g₃', hr11, BitVec.ofInt_natCast]
  have hin832 : InRegions s₃.wr (s₃.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)) 64 := by
    rw [wr₃, wr₂, hwr, e832]; exact in_sub hp.base.p_in (by decide)
  rw [WP.block_cons_iff]
  refine ⟨s₃.setMem (s₃.mem.writeW (pp s₀ + BitVec.ofNat 64 832) (s₃.zmm .xmm1)),
    by simp only [isa, exec, State.store512_eq, ea_at, hin832, ite_true]; rw [e832], WP.block_nil ?_⟩
  have k₅ : ∀ o, o + 16 ≤ 832 → (s₃.mem.writeW (pp s₀ + BitVec.ofNat 64 832) (s₃.zmm .xmm1)).readW
      (pp s₀ + BitVec.ofNat 64 o) 128 = s₃.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 := fun o ho =>
    Mem.readW_writeW_sep (Offset.sep (pp s₀) (d := o) (n := 128 / 8) (e := 832) (k := 512 / 8) (by omega_arith) (by omega_arith)
      (by omega_arith)) (by decide)
  have z13 : ∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 4, s₃.zlane r l = s.zlane r l :=
    fun r h7 h8 h9 h10 h12 l hl => by rw [z₃ r h7 h10 h12 l hl, z₂ r h7 h10 h12 l hl]
  refine ⟨fun g hg k hk l hl => ?_, fun l hl => ?_, fun o ho => ?_, ?_, by rw [State.setMem_gpr, g₃'],
    by rw [State.setMem_rd, rd₃, rd₂], by rw [State.setMem_wr, wr₃, wr₂],
    fun r h7 h8 h9 h10 h12 l hl => by rw [State.setMem_zlane, z13 r h7 h8 h9 h10 h12 l hl]⟩
  · rw [State.setMem_mem, k₅ _ (by simp only [tab]; omega_arith),
      show tab g + 64 * k + 16 * l = tab g + 32 * (2 * k + l / 2) + 16 * (l % 2) by omega_arith]
    rcases (by omega_arith : g = 0 ∨ g = 1) with rfl | rfl
    · rw [t₃ _ (by omega_arith) _ (by omega_arith), hH₂]; congr 2; omega_arith
    · rw [keepAt f₃ (by simp only [tab]; omega_arith) (by simp only [tab]; omega_arith) (by simp only [tab]; omega_arith),
        t₂ _ (by omega_arith) _ (by omega_arith)]; congr 2; omega_arith
  · rw [State.setMem_mem, show pp s₀ + BitVec.ofNat 64 (832 + 16 * l) = pp s₀ + BitVec.ofNat 64 832 + BitVec.ofNat 64 (16 * l) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add], readW_lane _ _ _ hl, zmm_lane _ _ hl,
      z13 _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl]
    exact h1 l hl
  · rw [State.setMem_mem, k₅ _ (by omega_arith), keepAt f₃ (by simp only [tab]; omega_arith) (by simp only [tab]; omega_arith) (by omega_arith),
      keepAt f₂ (by simp only [tab]; omega_arith) (by simp only [tab]; omega_arith) (by omega_arith)]
  · rw [State.setMem_mem]
    exact ((frame_pR (by simp only [tab]; omega_arith) f₂).trans (frame_pR (by simp only [tab]; omega_arith) f₃)).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

/-- The key context, with its powers, is kept by the loops, which write only
the data and the working space. -/
theorem ctx_keep {s₀ : State} (hp : SPrePrepared s₀) {m : Mem} (hf : Frame [dR s₀, pR s₀] s₀.mem m) :
    Spec.Gcm.PreparedPowersRepr m (kp s₀) ∧ Spec.Gcm.ctxH m (kp s₀) = hk s₀ := by
  have hwk := hp.wrap_k
  have kb : ∀ o, o + 16 ≤ 1024 → blockAt m (kp s₀ + BitVec.ofNat 64 o) = blockAt s₀.mem (kp s₀ + BitVec.ofNat 64 o) :=
    fun o ho => VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.d_k.symm.sub_left (Offset.sub_base _ ho)
      · exact hp.p_k.symm.sub_left (Offset.sub_base _ ho)
  have hH : Spec.Gcm.ctxH m (kp s₀) = hk s₀ := kb 240 (by decide)
  exact ⟨CtxMode.prepared.frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_k.symm
    · exact hp.p_k.symm) hp.wrap_k hp.pow, hH⟩

end VG.Proof.Gcm.X86_64.StitchZR

end

end

/-! ### `Gcm.X86_64.StitchZ.SetupP`, which only this module used -/

section

/-!
# The setup of the AVX-512 loops, from the powers in the key context

Untrusted: everything here is checked by Lean. `setupGP_ok`: `StitchZP.setupGP`
leaves what `Stitch.setupG` does (`Stitch.setupG_ok`): the constants in both
lanes of `ymm0` and `ymm1`, and in the lanes of `ymm3`–`ymm6`,
`ymm12`–`ymm15` the powers `H¹⁶⁻²ᵏ⁻ˡ · x⁻¹` (`hInvF`), each converted from
the power the key context holds (`cvtPair_ok`, `Spec.Gcm.PowersRepr`).
`setupP_ok`: then `StitchZ`'s rest of the setup (`Stitch.setupT_ok`,
`setupZ_ok`), as `StitchZ.setup_ok`, the field aside (`StitchZ/OkP.lean`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZP

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreP kp hk in_sub_int setupT_ok)
open VG.Proof.Gcm.X86_64.Pclmul (Only const_ok)
open VG.Impl.Gcm.X86_64.Pclmul (at_ xInv poly revMask)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZP (cvtConsts cvtPair setupGP setupP)

/-- `vinserti128 r, r, r, 1`: lane 0 copied to lane 1. -/
theorem vinsSelf_ok (r : XReg) (s : State) :
    WP isa (.block [.vop (.vinserti128 r r r 1)]) s fun s' =>
      (∀ l < 2, s'.lane r l = s.lane r 0) ∧ YFrame [r] s s' := by
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, rfl, rfl, rfl, rfl, fun r' hr l hl => ?_⟩⟩
  · rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl <;> simp [VOp.exec, State.setV, State.lane]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl <;> simp [hr, VOp.exec, State.setV, State.lane]

theorem preg16_ne (k : Nat) : preg16 k ≠ .xmm0 ∧ preg16 k ≠ .xmm1 ∧ preg16 k ≠ .xmm7 ∧ preg16 k ≠ .xmm8 ∧
    preg16 k ≠ .xmm9 ∧ preg16 k ≠ .xmm10 := by
  unfold preg16; split <;> decide

theorem preg16_inj : ∀ k < 8, ∀ k' < 8, preg16 k = preg16 k' → k = k' := by decide

/-- The registers the conversions write. -/
abbrev cvtRegs : List XReg := [.xmm7, .xmm10, .xmm3, .xmm4, .xmm5, .xmm6, .xmm15, .xmm14, .xmm13, .xmm12]

theorem preg16_mem (k : Nat) : preg16 k ∈ cvtRegs := by unfold preg16; split <;> decide

/-- The block of the key context at `256 + 16 k`, for `k < 48`, is `Hᵏ⁺¹`. -/
theorem pow_at {s₀ : State} (hp : SPreP s₀) {k : Nat} (hk48 : k < 48) :
    Spec.Gcm.blockAt s₀.mem (kp s₀ + BitVec.ofInt 64 ((256 + 16 * k : Nat) : Int)) = Spec.Gcm.hpow (hk s₀) (k + 1) := by
  rw [BitVec.ofInt_natCast, hp.pow k hk48]; rfl

/-- The pairs `0 … n - 1`. -/
theorem cvtRun_ok {s₀ : State} (hp : SPreP s₀) :
    ∀ n, n ≤ 8 → ∀ s, s.gpr .rdi = kp s₀ → s.mem = s₀.mem → s.rd = s₀.rd → s.wr = s₀.wr →
      (∀ l < 2, s.lane .xmm0 l = revMask) → (∀ l < 2, s.lane .xmm8 l = xInv) →
      (∀ l < 2, s.lane .xmm9 l = ones) →
      WP isa (.block ((List.range n).flatMap fun k => cvtPair (15 - 2 * k) (preg16 k))) s fun s' =>
        (∀ k < n, ∀ l < 2, s'.lane (preg16 k) l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * k - l))) ∧ YFrame cvtRegs s s'
  | 0, _, s, _, _, _, _, _, _, _ => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨fun k hk => absurd hk (by omega_using []), YFrame.refl _ _⟩
  | n + 1, hn, s, hdi, hm, hrd, hwr, h0, h8, h9 => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (cvtRun_ok hp n (by omega_using [hn]) s hdi hm hrd hwr h0 h8 h9) fun s₁ ⟨p₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨_, _, n7, n8, n9, n10⟩ := preg16_ne n
    have kin : ∀ o : Nat, o + 16 ≤ 1024 → InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofInt 64 (o : Int)) 16 :=
      fun o ho => by rw [f₁.rd, f₁.wr, f₁.gpr, hrd, hwr, hdi]; exact in_sub_int hp.k_in ho
    refine WP.mono (cvtPair_ok (15 - 2 * n) (preg16 n) n7 n8 n9 n10 s₁
      (fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact h0 l hl)
      (fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact h8 l hl)
      (fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact h9 l hl)
      (kin _ (by omega_using [])) (kin _ (by omega_using []))) fun s' ⟨v0, v1, f'⟩ => ⟨fun k hk l hl => ?_, ?_⟩
    · rw [f₁.mem, f₁.gpr, hm, hdi] at v0 v1
      by_cases hkn : k = n
      · subst hkn
        rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
        · rw [v0, pow_at hp (by omega_using [])]; congr 2; omega_using [hn]
        · rw [v1, show 240 + 16 * (15 - 2 * k) = 256 + 16 * (14 - 2 * k) by omega_using [hn], pow_at hp (by omega_using [])]
          congr 2; omega_using [hn]
      · rw [f'.lane _ (fun h => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h
          · exact (preg16_ne k).2.2.1 h
          · exact (preg16_ne k).2.2.2.2.2 h
          · exact hkn (preg16_inj k (by omega_using [hn, hk]) n (by omega_using [hn]) h)) l hl]
        exact p₁ k (by omega_using [hk, hkn]) l hl
    · refine ⟨f'.gpr.trans f₁.gpr, f'.mem.trans f₁.mem, f'.rd.trans f₁.rd, f'.wr.trans f₁.wr, fun r hr l hl => ?_⟩
      rw [f'.lane r (fun h => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · decide
        · decide
        · exact preg16_mem n)) l hl, f₁.lane r hr l hl]

/-- `setupGP`: what `Stitch.setupG_ok` says of `setupG`. -/
theorem setupGP_ok {s₀ : State} (hp : SPreP s₀) :
    WP isa (.block setupGP) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, s.lane (preg16 k) l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * k - l))) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  simp only [setupGP, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff, show ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] :
    List Instr) = [.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1)] ++ [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] from rfl,
    WP.block_append_iff]
  refine WP.mono (vinsSelf_ok .xmm0 s₂) fun s₃ ⟨v₃, f₃⟩ => ?_
  refine WP.mono (vinsSelf_ok .xmm1 s₃) fun s₄ ⟨v₄, f₄⟩ => ?_
  have m0 : ∀ l < 2, s₄.lane .xmm0 l = revMask := fun l hl => by
    rw [f₄.lane _ (by decide) l hl, v₃ l hl]; show s₂.xmm .xmm0 = _; rw [o₂.xmm _ (by decide), c₁]; rfl
  have m1 : ∀ l < 2, s₄.lane .xmm1 l = poly := fun l hl => by
    rw [v₄ l hl, f₃.lane _ (by decide) 0 (by decide)]; exact c₂
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₄ m1) fun s₅ ⟨c8, c9, f₅⟩ => ?_
  have g₅ : ∀ r, r ≠ .rax → s₅.gpr r = s₀.gpr r := fun r hr => by rw [f₅.gpr, f₄.gpr, f₃.gpr, o₁₂.gpr r hr]
  have mm₅ : s₅.mem = s₀.mem := by rw [f₅.mem, f₄.mem, f₃.mem, o₁₂.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [f₅.rd, f₄.rd, f₃.rd, o₁₂.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [f₅.wr, f₄.wr, f₃.wr, o₁₂.wr]
  refine WP.mono (cvtRun_ok hp 8 (Nat.le_refl _) s₅ (g₅ _ (by decide)) mm₅ rd₅ wr₅
    (fun l hl => by rw [f₅.lane _ (by decide) l hl]; exact m0 l hl) c8 c9) fun s' ⟨pw, F⟩ =>
    ⟨fun l hl => by rw [F.lane _ (by decide) l hl, f₅.lane _ (by decide) l hl]; exact m0 l hl,
      fun l hl => by rw [F.lane _ (by decide) l hl, f₅.lane _ (by decide) l hl]; exact m1 l hl, pw,
      fun r hr => by rw [F.gpr, g₅ r hr], by rw [F.mem, mm₅], by rw [F.rd, rd₅], by rw [F.wr, wr₅]⟩

/-- `setupP`: the state the AVX-512 loops start from, with the powers
`Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ · x⁻¹` in the working space, as `StitchZ.setup_ok`. -/
theorem setupP_ok {s₀ : State} (hp : SPreP s₀) :
    WP isa (.block setupP) s₀ fun s => ∃ P, StitchZ.Ready s₀ P s ∧
      ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)) := by
  rw [setupP, List.append_assoc, List.append_assoc, WP.block_append_iff, ← List.append_assoc]
  refine WP.mono (setupGP_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (setupT_ok hp.base l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => WP.mono (StitchZ.setupZ_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega_using []]
      exact pw _ (by omega_using [hk, hl]) _ (by omega_using [])⟩

end VG.Proof.Gcm.X86_64.StitchZP

end

end


/-! # Preparing the AVX-512 loop state by loading encoded powers -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZR
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPrePrepared kp hk in_sub_int setupT_ok)
open VG.Proof.Gcm.X86_64.Pclmul (const_ok)
open VG.Impl.Gcm.X86_64.Pclmul (poly revMask)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZR (cvtPair setupGP setupP)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF vinsSelf_ok cvtRegs preg16_mem preg16_inj)

/-- Load the first `n` register pairs from the prepared context. -/
theorem cvtRun_ok {s₀ : State} {lo np : Nat} (hp : SPrePrepared s₀ lo np) (h8 : 8 ≤ np) :
    ∀ n, n ≤ 8 → ∀ s, s.gpr .rdi = kp s₀ → s.mem = s₀.mem → s.rd = s₀.rd → s.wr = s₀.wr →
      WP isa (.block ((List.range n).flatMap fun k => cvtPair (15 - 2*k) (preg16 k))) s fun s' =>
        (∀ k < n, ∀ l < 2, s'.lane (preg16 k) l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2*k - l))) ∧
        YFrame cvtRegs s s'
  | 0, _, s, _, _, _, _ => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨fun k hk => absurd hk (by omega_using []), YFrame.refl _ _⟩
  | n+1, hn, s, hdi, hm, hrd, hwr => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (cvtRun_ok hp h8 n (by omega_using [hn]) s hdi hm hrd hwr) fun s₁ ⟨p₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hin : InRegions (s₁.rd ++ s₁.wr)
        (s₁.gpr .rdi + BitVec.ofInt 64 ((240 + 16*(15-2*n) : Nat) : Int)) 32 := by
      rw [f₁.rd, f₁.wr, f₁.gpr, hrd, hwr, hdi]
      exact in_sub_int hp.k_in (by omega_using [])
    refine WP.mono (loadPair_ok (15-2*n) (preg16 n) s₁ hin) fun s' ⟨v, z⟩ => ?_
    have f := z.yframe
    refine ⟨fun k hk l hl => ?_, f₁.trans (f.mono fun r hr => ?_)⟩
    · by_cases hkn : k = n
      · subst k
        rw [v l hl, f₁.mem, hm, f₁.gpr, hdi,
          pair_values hp.pow (by omega_using [h8]) (by omega_using [hn]) hl]
        congr 2; omega_using [hn]
      · rw [f.lane _ (fun h => hkn (preg16_inj k (by omega_using [hn, hk]) n (by omega_using [hn]) (List.mem_singleton.mp h))) l hl]
        exact p₁ k (by omega_using [hk, hkn]) l hl
    · have e := List.mem_singleton.mp hr
      subst r
      exact preg16_mem n

/-- `setupGP`: what `Stitch.setupG_ok` says of `setupG`. -/
theorem setupGP_ok {s₀ : State} {lo np : Nat} (hp : SPrePrepared s₀ lo np) (h8 : 8 ≤ np := by decide) :
    WP isa (.block setupGP) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, s.lane (preg16 k) l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * k - l))) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  simp only [setupGP, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff, show ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] :
    List Instr) = [.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1)] ++ [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] from rfl,
    WP.block_append_iff]
  refine WP.mono (vinsSelf_ok .xmm0 s₂) fun s₃ ⟨v₃, f₃⟩ => ?_
  refine WP.mono (vinsSelf_ok .xmm1 s₃) fun s₄ ⟨v₄, f₄⟩ => ?_
  have m0 : ∀ l < 2, s₄.lane .xmm0 l = revMask := fun l hl => by
    rw [f₄.lane _ (by decide) l hl, v₃ l hl]; show s₂.xmm .xmm0 = _; rw [o₂.xmm _ (by decide), c₁]; rfl
  have m1 : ∀ l < 2, s₄.lane .xmm1 l = poly := fun l hl => by
    rw [v₄ l hl, f₃.lane _ (by decide) 0 (by decide)]; exact c₂
  have g₄ : ∀ r, r ≠ .rax → s₄.gpr r = s₀.gpr r := fun r hr => by rw [f₄.gpr, f₃.gpr, o₁₂.gpr r hr]
  have mm₄ : s₄.mem = s₀.mem := by rw [f₄.mem, f₃.mem, o₁₂.mem]
  have rd₄ : s₄.rd = s₀.rd := by rw [f₄.rd, f₃.rd, o₁₂.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [f₄.wr, f₃.wr, o₁₂.wr]
  refine WP.mono (cvtRun_ok hp h8 8 (Nat.le_refl _) s₄ (g₄ _ (by decide)) mm₄ rd₄ wr₄)
    fun s' ⟨pw, F⟩ =>
    ⟨fun l hl => by rw [F.lane _ (by decide) l hl]; exact m0 l hl,
      fun l hl => by rw [F.lane _ (by decide) l hl]; exact m1 l hl, pw,
      fun r hr => by rw [F.gpr, g₄ r hr], by rw [F.mem, mm₄], by rw [F.rd, rd₄], by rw [F.wr, wr₄]⟩

/-- `setupP`: the state the AVX-512 loops start from, with the powers
`Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ · x⁻¹` in the working space, as `StitchZ.setup_ok`. -/
theorem setupP_ok {s₀ : State} (hp : SPrePrepared s₀) :
    WP isa (.block setupP) s₀ fun s => ∃ P, StitchZ.Ready s₀ P s ∧
      ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)) := by
  rw [setupP, List.append_assoc, List.append_assoc, WP.block_append_iff, ← List.append_assoc]
  refine WP.mono (setupGP_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (setupT_ok hp.base l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => WP.mono (StitchZ.setupZ_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega_using []]
      exact pw _ (by omega_using [hk, hl]) _ (by omega_using [])⟩

end VG.Proof.Gcm.X86_64.StitchZR
