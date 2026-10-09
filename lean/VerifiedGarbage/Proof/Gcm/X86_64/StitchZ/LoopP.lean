import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.SetupP
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48

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
  exact ⟨fun k hk => by rw [kblk hp hf (by omega), h k hk, hH], hH⟩

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
  refine WP.mono (cvt12_ok (48 - 16 * g - 2 * m - 1) s E.m0 E.c8 E.c9 (kin _ (by omega)) (kin _ (by omega)))
    fun s₁ ⟨⟨v0, v1, _⟩, z₁⟩ => ?_
  have j32 : 32 * (16 - 8 * g + m) = tab g + 32 * m := by simp only [tab]; omega
  have hin : ∀ k < [XReg.xmm12].length, InRegions s₁.wr (s₁.gpr .r11 + BitVec.ofInt 64 ((32 * (16 - 8 * g + m + k) : Nat) : Int)) 32 :=
    fun k hk => by
      simp only [List.length_singleton] at hk
      rw [z₁.wr, z₁.gpr, E.wr, E.r11]; exact in_sub_int hp.base.p_in (by simp only [tab] at j32; omega)
  refine WP.mono (WP.block_and (storesK_ok .r11 [.xmm12] _ s₁ hin
      (by rw [z₁.gpr, E.r11]; simp only [tab] at j32; simp; omega))
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
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [v0, powm E.pow (by omega)]; congr 2; omega
  · rw [v1, show 240 + 16 * (48 - 16 * g - 2 * m - 1) = 256 + 16 * (48 - 16 * g - 2 * m - 2) by omega,
      powm E.pow (by omega)]; congr 2; omega

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
    exact WP.block_nil ⟨fun m hm => absurd hm (by omega), Frame.refl _ _, rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl⟩
  | n + 1, hn, s, E => by
    have hwp := hp.base.wrap_p
    have htab : tab g ≤ 512 := by simp only [tab]; omega
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (powRun_ok hp hg n (by omega) s E) fun s₁ ⟨p₁, f₁, g₁, rd₁, wr₁, z₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨pw₁, hH₁⟩ := pow_frame hp (frame_pR (by omega) f₁) E.pow
    have lk : ∀ r ∈ ([.xmm0, .xmm8, .xmm9] : List XReg), ∀ l < 2, s₁.lane r l = s.lane r l := fun r hr l hl => by
      rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact z₁ _ (by decide) (by decide) (by decide) l (by omega)
    have E₁ : CvtEnv s₀ s₁ := ⟨by rw [g₁]; exact E.rdi, by rw [g₁]; exact E.r11, by rw [rd₁]; exact E.rd,
      by rw [wr₁]; exact E.wr, pw₁, fun l hl => by rw [lk _ (by simp) l hl]; exact E.m0 l hl,
      fun l hl => by rw [lk _ (by simp) l hl]; exact E.c8 l hl, fun l hl => by rw [lk _ (by simp) l hl]; exact E.c9 l hl⟩
    refine WP.mono (powPair_ok hp hg (by omega : n < 8) E₁) fun s' ⟨v, f', g', rd', wr', z'⟩ => ⟨fun m hm l hl => ?_,
      (frame_sub (Nat.le_refl _) (by omega) f₁).trans (frame_sub (by omega) (by omega) f'),
      by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁],
      fun r h7 h10 h12 l hl => by rw [z' r h7 h10 h12 l hl, z₁ r h7 h10 h12 l hl]⟩
    by_cases hmn : m = n
    · subst hmn; rw [v l hl, hH₁]
    · rw [keepAt f' (by omega) (by omega) (by omega)]; exact p₁ m (by omega) l hl

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
  refine WP.mono (WP.block_and (consts_ok s fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact h1 l (by omega))
    (WP.zframe (rs := [.xmm8, .xmm9]) (by decide) (Q := fun _ => True)
      (WP.of_runBlock ⟨_, (zframe_block [.xmm8, .xmm9] cvtConsts (by decide) s).choose_spec.1, trivial⟩)))
    fun s₁ ⟨⟨c8, c9, _⟩, _, z₁⟩ => ?_
  have l₁ : ∀ r, r ≠ .xmm8 → r ≠ .xmm9 → ∀ l < 4, s₁.zlane r l = s.zlane r l :=
    fun r h8 h9 l hl => z₁.zlane r (by simp [h8, h9]) l hl
  have m0₁ : ∀ l < 2, s₁.lane .xmm0 l = revMask := fun l hl => by
    rw [← State.zlane_lt2 _ _ hl, l₁ _ (by decide) (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact m0 l hl
  have E₁ : CvtEnv s₀ s₁ := ⟨by rw [z₁.gpr]; exact hdi, by rw [z₁.gpr]; exact hr11, by rw [z₁.rd]; exact hrd,
    by rw [z₁.wr]; exact hwr, by rw [z₁.mem]; exact hpw, m0₁, c8, c9⟩
  rw [WP.block_append_iff]
  refine WP.mono (powRun_ok hp (g := 1) (by decide) 8 (Nat.le_refl _) s₁ E₁) fun s₂ ⟨t₂, f₂, g₂, rd₂, wr₂, z₂⟩ => ?_
  obtain ⟨pw₂, hH₂⟩ := pow_frame hp (frame_pR (by simp only [tab]; omega) f₂) E₁.pow
  have lk : ∀ r ∈ ([.xmm0, .xmm8, .xmm9] : List XReg), ∀ l < 2, s₂.lane r l = s₁.lane r l := fun r hr l hl => by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact z₂ _ (by decide) (by decide) (by decide) l (by omega)
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
    Mem.readW_writeW_sep (Offset.sep (pp s₀) (d := o) (n := 128 / 8) (e := 832) (k := 512 / 8) (by omega) (by omega)
      (by omega)) (by decide)
  have z13 : ∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 4, s₃.zlane r l = s.zlane r l :=
    fun r h7 h8 h9 h10 h12 l hl => by rw [z₃ r h7 h10 h12 l hl, z₂ r h7 h10 h12 l hl, l₁ r h8 h9 l hl]
  refine ⟨fun g hg k hk l hl => ?_, fun l hl => ?_, fun o ho => ?_, ?_, by rw [State.setMem_gpr, g₃'],
    by rw [State.setMem_rd, rd₃, rd₂, z₁.rd], by rw [State.setMem_wr, wr₃, wr₂, z₁.wr],
    fun r h7 h8 h9 h10 h12 l hl => by rw [State.setMem_zlane, z13 r h7 h8 h9 h10 h12 l hl]⟩
  · rw [State.setMem_mem, k₅ _ (by simp only [tab]; omega),
      show tab g + 64 * k + 16 * l = tab g + 32 * (2 * k + l / 2) + 16 * (l % 2) by omega]
    rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
    · rw [t₃ _ (by omega) _ (by omega), hH₂, z₁.mem]; congr 2; omega
    · rw [keepAt f₃ (by simp only [tab]; omega) (by simp only [tab]; omega) (by simp only [tab]; omega),
        t₂ _ (by omega) _ (by omega), z₁.mem]; congr 2; omega
  · rw [State.setMem_mem, show pp s₀ + BitVec.ofNat 64 (832 + 16 * l) = pp s₀ + BitVec.ofNat 64 832 + BitVec.ofNat 64 (16 * l) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add], readW_lane _ _ _ hl, zmm_lane _ _ hl,
      z13 _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl]
    exact h1 l hl
  · rw [State.setMem_mem, k₅ _ (by omega), keepAt f₃ (by simp only [tab]; omega) (by simp only [tab]; omega) (by omega),
      keepAt f₂ (by simp only [tab]; omega) (by simp only [tab]; omega) (by omega), z₁.mem]
  · rw [State.setMem_mem, ← z₁.mem]
    exact ((frame_pR (by simp only [tab]; omega) f₂).trans (frame_pR (by simp only [tab]; omega) f₃)).writeW
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
  rw [kb _ (by omega), hp.pow k hk, hH]; rfl

/-- `bigP`: `big` with the tables loaded. -/
theorem bigP_ok {s₀ : State} (hp : SPreP s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) (h256 : 256 ≤ nb s₀) {s : State}
    (hI : EInv s₀ P 1 s) : WP isa bigP s fun s' => ∃ e, EInv s₀ P e s' := by
  have hdi : s.gpr .rdi = kp s₀ := hI.gpr .rdi (by decide) (by decide) (by decide) (by decide)
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hpw, hH⟩ := ctx_keep hp hI.a.frame
  refine WP.seq (WP.mono (powP48_ok hp hdi hr11 hI.a.rd hI.a.wr hpw
    (fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact hI.a.msk l (by omega)) hI.m1)
    fun s₁ ⟨t, pm, keep, fr, g₁, rd₁, wr₁, z₁⟩ => ?_)
  rw [hH] at t
  let T : Nat → Nat → Nat → Block := fun g k l =>
    if g = 2 then P k l else s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128
  have hv : ∀ g < 3, ∀ k < 4, ∀ l < 4,
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l := fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2
      simp only [T, ↓reduceIte, show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega]
      rw [keep _ (by omega)]; exact hI.pw k hk l hl
    · simp only [T, h2, ↓reduceIte]
  have hT : FinOk48 (hk s₀) T := hFin T fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2; simp only [T, ↓reduceIte]; rw [hP k hk l hl]
    · simp only [T, h2, ↓reduceIte]; exact t g (by omega) k hk l hl
  exact bigRest_ok hp.base hm hf hT (fun k l => by simp only [T, ↓reduceIte]) h256 hI
    (hI.a.pow hp.base fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl) hv pm g₁
    fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl

/-- `bigDP`: `bigD` with the tables loaded. -/
theorem bigDP_ok {s₀ : State} (hp : SPreP s₀) {P : Nat → Nat → Block}
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) (h256 : 256 ≤ nb s₀) {s : State}
    (hI : DInv s₀ P 0 s) : WP isa bigDP s fun s' => ∃ e, DInv s₀ P e s' := by
  have hdi : s.gpr .rdi = kp s₀ := hI.gpr .rdi (by decide) (by decide) (by decide) (by decide)
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hpw, hH⟩ := ctx_keep hp hI.a.frame
  refine WP.seq (WP.mono (powP48_ok hp hdi hr11 hI.a.rd hI.a.wr hpw
    (fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact hI.a.msk l (by omega)) hI.m1)
    fun s₁ ⟨t, pm, keep, fr, g₁, rd₁, wr₁, z₁⟩ => ?_)
  rw [hH] at t
  let T : Nat → Nat → Nat → Block := fun g k l =>
    if g = 2 then P k l else s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128
  have hv : ∀ g < 3, ∀ k < 4, ∀ l < 4,
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l := fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2
      simp only [T, ↓reduceIte, show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega]
      rw [keep _ (by omega)]; exact hI.pw k hk l hl
    · simp only [T, h2, ↓reduceIte]
  have hT : FinOk48 (hk s₀) T := hFin T fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2; simp only [T, ↓reduceIte]; rw [hP k hk l hl]
    · simp only [T, h2, ↓reduceIte]; exact t g (by omega) k hk l hl
  exact bigDRest_ok hp.base hT (fun k l => by simp only [T, ↓reduceIte]) h256 hI
    (hI.a.pow hp.base fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl) hv pm g₁
    fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl

end VG.Proof.Gcm.X86_64.StitchZP
