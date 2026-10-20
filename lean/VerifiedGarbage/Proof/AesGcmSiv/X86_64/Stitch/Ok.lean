module
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Enc
public import VerifiedGarbage.Proof.Gcm.Poly

import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec

/-!
# AES-GCM-SIV's interleaved loop: the powers, and the whole loop

`setupG_ok`: the setup computes `H'`–`H'¹⁶` (`x · H'ᵏ = Hᵏ`) from `H` at
`r8`, as AES-GCM's from its hash subkey (`Proof.Gcm.X86_64.Stitch.setupG_ok`);
with the rest of the setup (`setupT_ok`), the state the loop starts from
(`Ready`). `dec_ok`: with those powers, whose products add up to `GHASH`
(`Proof.Gcm.X86_64.Stitch.finE`), the loop meets `DPost`. `hash_ok`: the
same powers, and the same loads, absorb the groups of sealing's POLYVAL
loop (`HPost`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (pows_ok const_ok ldrev_ok hInv_ok rev_eq)
open VG.Proof.Gcm.X86_64.Vpclmul (powersP_ok powers16P_ok)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.AesGcmSiv.X86_64Stitch (setupG setup dec)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Stitch (finE)

theorem setupG_ok {s₀ : State} (hh : InRegions (s₀.rd ++ s₀.wr) (hp s₀) 16) :
    WP isa (.block setupG) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, x * φ (s.lane (preg16 k) l) = φ (hk s₀) ^ (16 - 2 * k - l)) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  simp only [setupG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .r8 0 s₂ (by decide)
    (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide), BitVec.ofInt_natCast, BitVec.add_zero]; exact hh))
    fun s₃ ⟨l₃, o₃⟩ => ?_
  have o₁₃ := o₁₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₃) fun s₄ ⟨t₄, o₄⟩ => ?_
  have hH : x * φ (s₄.xmm .xmm3) = φ (hk s₀) := by
    rw [t₄, l₃, o₁₂.mem, o₁₂.gpr _ (by decide), BitVec.ofInt_natCast, BitVec.add_zero]
  rw [WP.block_append_iff]
  refine WP.mono (pows_ok s₄ (by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]) hH)
    fun s₇ ⟨hH2, hH3, hH4, o₇⟩ => ?_
  have o₁₇ := o₁₃.trans (o₄.trans o₇)
  rw [WP.block_append_iff]
  refine WP.mono (powersP_ok (H := hk s₀)
    (by rw [(o₂.trans (o₃.trans (o₄.trans o₇))).xmm _ (by decide), c₁, rev_eq])
    (by rw [(o₃.trans (o₄.trans o₇)).xmm _ (by decide), c₂])
    (by rw [o₇.xmm _ (by decide), hH]) hH2 hH3 hH4)
    fun s₈ ⟨l0, l1, _, pw8, _, g₈, m₈, rd₈, wr₈⟩ => ?_
  refine WP.mono (powers16P_ok l1 pw8) fun s₉ ⟨pw, F⟩ => ⟨fun l hl => ?_, fun l hl => ?_, pw,
    fun r hr => by rw [F.gpr, g₈ r hr, o₁₇.gpr r hr], by rw [F.mem, m₈, o₁₇.mem],
    by rw [F.rd, rd₈, o₁₇.rd], by rw [F.wr, wr₈, o₁₇.wr]⟩
  · rw [F.lane _ (by decide) l hl]; exact l0 l hl
  · rw [F.lane _ (by decide) l hl]; exact l1 l hl

theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P, Ready s₀ P s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  simp only [setup, List.append_assoc]
  rw [WP.block_append_iff]
  exact WP.mono (setupG_ok hp.h_in) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ =>
    WP.mono (setupT_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => ⟨_, hR, pw⟩

/-- The loop, on `n` blocks (a multiple of 16, at least 16). -/
theorem dec_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) : WP isa dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw⟩ => decTail_ok hp hm (finE hpw) hR)


/-! ## Sealing: POLYVAL of the groups

`hash_ok`: `Impl.AesGcmSiv.X86_64Stitch.hash` absorbs the `r9` blocks at
`rdx` (a multiple of 16, at least 16) into `Y` at `rcx`, each the field
element of its 16 bytes as they are, with GHASH and the key `H` at `r8`, as
the interleaved loop does (`DPost.y`): the powers as its setup computes them
(`setupG_ok`), then a body per group, the loads of `dec`'s last group
(`ghRun_ok`, `ghFin`). `HPre` is what it needs, `HPost` what it does.
-/

section Hash

open VG VG.X86_64
open VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs ordE)
open VG.Impl.AesGcmSiv.X86_64Stitch (setupG loadY hbody hash lastG storeY)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Stitch (in_sub in_sub_int in_rdwr FinOk storesK_ok store16_ok ghash_append16 finE)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom)

section
variable (s₀ : State)

/-- The data hashed: `rdx`. -/
abbrev xp : Addr := s₀.gpr .rdx
abbrev xR : Region := ⟨xp s₀, 16 * nb s₀⟩
/-- Its block `k`, as POLYVAL's field element. -/
abbrev xel (k : Nat) : Block := Spec.GcmSiv.ofBytes (bytesAt s₀.mem (xp s₀ + BitVec.ofNat 64 (16 * k)) 16)

end

structure HPre (s₀ : State) : Prop where
  nb16 : 16 ≤ nb s₀
  nm : nb s₀ % 16 = 0
  h_in : InRegions (s₀.rd ++ s₀.wr) (hp s₀) 16
  y_in : InRegions s₀.wr (yp s₀) 16
  x_in : InRegions (s₀.rd ++ s₀.wr) (xp s₀) (16 * nb s₀)
  p_in : InRegions s₀.wr (pp s₀) 256
  p_y : (pR s₀).Disjoint (yR s₀)
  p_x : (pR s₀).Disjoint (xR s₀)
  wrap_x : (xp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  wrap_p : (pp s₀).toNat + 256 ≤ 2 ^ 64

/-- What it leaves: `Y` continued over the blocks, nothing else written but
the working space. -/
structure HPost (s₀ s : State) : Prop where
  y : blockAt s.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) ((List.range (nb s₀)).map (xel s₀))
  frame : Frame [yR s₀, pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `Y` from `rcx`, in GHASH's order. -/
theorem loadY_ok (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask) (hy : InRegions s.wr (s.gpr .rcx) 16) :
    WP isa (.block loadY) s fun s' =>
      s'.lane .xmm2 0 = blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm2 1 = 0 ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm2 → ∀ l < 2, s'.lane r l = s.lane r l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hy
  have m0 := h0 0 (by decide)
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [loadY, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    isa, State.setV, State.load128, State.lane, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', VBinOp.sse,
    Option.map_some, Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, trivial, trivial, fun r h2 l hl => ?_, trivial, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2]

/-- The hashing loop's state: `g` groups absorbed into `Y` (in `xmm2`). -/
structure HInv (s₀ : State) (P : Nat → Nat → Block) (g : Nat) (s : State) : Prop where
  rdx : s.gpr .rdx = xp s₀ + BitVec.ofNat 64 (256 * g)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * g)
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  frame : Frame [pR s₀] s₀.mem s.mem
  m0 : ∀ l < 2, s.lane .xmm0 l = revMask
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * g)).map (xel s₀))
  y1 : s.lane .xmm2 1 = 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The setup: the powers, stored, and `Y`. -/
theorem hsetup_ok {s₀ : State} (hp : HPre s₀) :
    WP isa (.block (setupG ++ storesK .r11 pregs 0 ++ loadY)) s₀ fun s => ∃ P, HInv s₀ P 0 s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  have hwp := hp.wrap_p
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupG_ok hp.h_in) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  have hr11 : s₁.gpr .r11 = pp s₀ := g₁ _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .r11 pregs 0 s₁ (fun k hk => by
      rw [wr₁, hr11]; exact in_sub_int hp.p_in (by simp [pregs] at hk; omega))
    (by rw [hr11]; simp [pregs]; omega)) fun s₂ ⟨sv, fr, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [hr11, Nat.mul_zero, BitVec.add_zero, show 32 * pregs.length = 256 from rfl, m₁] at fr
  replace fr : Frame [pR s₀] s₀.mem s₂.mem := fr.sub fun r hr => ⟨pR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  refine WP.mono (loadY_ok s₂ (fun l hl => by rw [l₂]; exact l0 l hl)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.y_in))
    fun s₃ ⟨y0, y1, g₃, lk, m₃, rd₃, wr₃⟩ => ⟨_, ⟨?_, ?_, fun r h1 _ _ => ?_, fun k hk l hl => ?_, ?_,
      fun l hl => ?_, fun l hl => ?_, ?_, y1, ?_, ?_⟩, pw⟩
  · rw [g₃, g₂, g₁ _ (by decide), Nat.mul_zero, BitVec.add_zero]
  · rw [g₃, g₂, g₁ _ (by decide), Nat.mul_zero, Nat.sub_zero]; simp
  · rw [g₃, g₂, g₁ r h1]
  · rw [m₃, show pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l) = s₁.gpr .r11 + BitVec.ofNat 64 (32 * (0 + k) + 16 * l)
      by rw [hr11, Nat.zero_add], sv k (by simp [pregs]; omega) l hl, pregs_get]
  · rw [m₃]; exact fr
  · rw [lk _ (by decide) l hl, l₂]; exact l0 l hl
  · rw [lk _ (by decide) l hl, l₂]; exact l1 l hl
  · rw [y0, g₂, g₁ _ (by decide), Proof.AesGcm.X86_64.blockAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.p_y.symm)]
    simp [ghashFrom]
  · rw [rd₃, rd₂, rd₁]
  · rw [wr₃, wr₂, wr₁]

/-- A body: the group at `rdx` absorbed. -/
theorem hbody_ok {s₀ : State} (hp : HPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {g : Nat}
    (hg : 16 * (g + 1) ≤ nb s₀) {s : State} (hI : HInv s₀ P g s) :
    WP isa (.block hbody) s fun s' => HInv s₀ P (g + 1) s' ∧ s'.zf = some (decide (nb s₀ - 16 * (g + 1) = 0)) := by
  have hw := hp.wrap_x
  have hwp := hp.wrap_p
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => xel s₀ (16 * g + i)
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide)
  have hoff : ∀ i, a + BitVec.ofNat 64 i = xp s₀ + BitVec.ofNat 64 (256 * g + i) := fun i => by
    show s.gpr .rdx + _ = _; rw [hI.rdx, add_ofNat_assoc]
  simp only [hbody, lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s) fun s₂ ⟨z₂, f₂, _⟩ => ?_
  have hE₂ : GEnv s₀ 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr]
      r11 := by rw [f₂.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₂.mem, hoff, hI.frame.readW (r := ⟨xp s₀ + BitVec.ofNat 64 (256 * g + 16 * i), 16⟩)
            (Region.contains_self _ _)
            (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact hp.p_x.symm.sub_left (Offset.sub_base _ (by omega))) (by decide),
          readW_ofBytes, show 256 * g + 16 * i = 16 * (16 * g + i) by omega]
      pv := fun k hk l hl => by rw [f₂.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, hI.rd, hI.wr, BitVec.ofInt_natCast, hoff]
        exact in_sub hp.x_in (by omega)
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, hI.rd, hI.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega)) }
  rw [WP.block_append_iff]
  refine WP.mono (ghRun_ok (yl := yl) 8 (Nat.le_refl _) s₂ hE₂ z₂
    (fun l hl => by rw [f₂.lane _ (by decide) l hl])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (fun l hl => by
      rw [f₃.lane _ (by decide) l hl, f₂.lane _ (by decide) l hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, y41, f₄⟩ => ?_
  rw [p₃ 0 (by decide), p₃ 1 (by decide)] at y4
  refine WP.mono (nextC_ok s₄) fun s' ⟨frdx, fr9, fzf, fg, fl, fm, frd, fwr⟩ => ?_
  have lk : ∀ r, r ≠ .xmm2 → r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → r ≠ .xmm12 →
      ∀ l < 2, s'.lane r l = s.lane r l := fun r h2 h7 h8 h9 h10 h11 h12 l hl => by
    rw [fl, f₄.lane _ (by simp [h2, h7, h8, h9, h10, h11]) l hl, f₃.lane _ (by simp [h7, h8, h9, h10, h11, h12]) l hl,
      f₂.lane _ (by simp [h8, h9, h10]) l hl]
  have lk7 : ∀ r ∈ ([.xmm0, .xmm1] : List XReg), ∀ l < 2, s'.lane r l = s.lane r l := fun r hr l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      exact lk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl
  have g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, f₂.gpr]
  have m₄ : s₄.mem = s.mem := by rw [f₄.mem, f₃.mem, f₂.mem]
  have hr9 : s₄.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (g + 1)) := by
    rw [g₄, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
  refine ⟨⟨?_, by rw [fr9, hr9], fun r h1 h2 h3 => by rw [fg r h2 h3, g₄]; exact hI.gpr r h1 h2 h3,
    fun k hk l hl => by rw [fm, m₄]; exact hI.pw k hk l hl, by rw [fm, m₄]; exact hI.frame,
    fun l hl => by rw [lk7 _ (by decide) l hl]; exact hI.m0 l hl,
    fun l hl => by rw [lk7 _ (by decide) l hl]; exact hI.m1 l hl,
    ?_, by rw [fl]; exact y41, by rw [frd, f₄.rd, f₃.rd, f₂.rd]; exact hI.rd,
    by rw [fwr, f₄.wr, f₃.wr, f₂.wr]; exact hI.wr⟩, ?_⟩
  · rw [frdx, g₄, hI.rdx, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, add_ofNat_assoc]
    congr 2
  · rw [fl, y4]
    refine (hf X yl hI.y1).trans ?_
    rw [ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · rw [fzf, hr9]
    simp only [Option.some.injEq]
    by_cases h : nb s₀ - 16 * (g + 1) = 0
    · simp [h]
    · simp only [h, decide_false]
      exact beq_false_of_ne fun h' => h (by
        have := congrArg BitVec.toNat h'
        rwa [toNat_ofNat_lt (by omega)] at this)

/-- `Y` stored. -/
theorem hfin_ok {s₀ : State} (hp : HPre s₀) {P : Nat → Nat → Block} {g : Nat} (hg : nb s₀ = 16 * g) {s : State}
    (hI : HInv s₀ P g s) : WP isa (.block storeY) s (HPost s₀) := by
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide)
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s (hI.m0 0 (by decide)) (by
      rw [hI.wr, hrcx]; exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx] at m₅
  refine ⟨?_, ?_, fun r h1 h2 h3 => ?_, by show s₅.rd = _; rw [rd₅, hI.rd], by show s₅.wr = _; rw [wr₅, hI.wr]⟩
  · show blockAt s₅.mem (yp s₀) = _
    rw [m₅, VG.Proof.Gcm.X86_64.blockAt_store, hI.y, hg]
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact (hI.frame.mono fun r hr => by simp at hr ⊢; simp [hr]).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · show s₅.gpr r = _
    rw [g₅]; exact hI.gpr r h1 h2 h3

/-- POLYVAL of the groups. -/
theorem hash_ok {s₀ : State} (hp : HPre s₀) : WP isa hash s₀ (HPost s₀) := by
  have h16 := hp.nb16
  have hm := hp.nm
  refine WP.seq (WP.mono (hsetup_ok hp) fun s₁ ⟨P, hI₁, hpw⟩ => WP.seq ?_)
  have hf : FinOk ordE (hk s₀) P := finE hpw
  let I : Nat → State → Prop := fun m s => ∃ g, m = nb s₀ - 16 * g ∧ 16 * (g + 1) ≤ nb s₀ ∧ HInv s₀ P g s
  have hstep : ∀ m s, I m s → WP isa (.block hbody) s (fun s' =>
      (eval .ne s' = some false ∧ ∃ g, nb s₀ = 16 * g ∧ HInv s₀ P g s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨g, rfl, hg, hI⟩
    refine WP.mono (hbody_ok hp hf hg hI) fun s' ⟨hI', hzf⟩ => ?_
    by_cases h0 : nb s₀ - 16 * (g + 1) = 0
    · exact .inl ⟨by simp only [eval, hzf, h0, decide_true, Option.map_some, Bool.not_true],
        g + 1, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hzf, h0, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (g + 1), by omega, g + 1, rfl, by omega, hI'⟩
  exact WP.mono (WP.loop (M := isa) I hstep (nb s₀ - 16 * 0) s₁ ⟨0, rfl, by omega, hI₁⟩)
    fun s ⟨g, hg, hI⟩ => hfin_ok hp hg hI

end Hash

end VG.Proof.AesGcmSiv.X86_64.Stitch
