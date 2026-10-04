import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
import VerifiedGarbage.Proof.Framework.X86_64.ZLaneSse
import VerifiedGarbage.Proof.Framework.X86_64.ZFrameBlock

/-!
# Interleaved counter mode and GHASH with AVX-512: the GHASH of a group

`ghLoad_ok`: `StitchZ.ghLoad k` loads four powers from the working space
into `zmm12` and blocks `4k`–`4k + 3` into the lanes of `zmm7`, and adds
their products to each lane's (`WP.zlanes` of `Vpclmul.ldacc_ok`, the SSE
code of each lane). `fin_ok`: `StitchZ.fin` adds lanes 2 and 3 of the
products to lanes 0 and 1 (`fold_ok`), reduces both and adds them into `Y`
(`Vpclmul.reduce_lanes`, `combine_ok`). The four lanes' products, so added
and reduced, are `GHASH` over the sixteen blocks (`finZ`).

`GEnv`, `ghStep`, `QG` and `gq_ok` are `Stitch`'s, with four lanes, one
batch per group and the reduction after round 5.
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp pp cb dp dR pR bAddr blk ctb ciph sch hk y₀ ite_t ite_f zero_xor_b)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce φ_reduce prod)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Proof.Gcm.X86_64.Vpclmul (ldacc ldacc_ok reduce_lanes)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (ghLoad acc ord foldLanes fin gq)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Proof.Gcm.X86_64.Pclmul (ea_at)
open VG.Proof.Aes.X86_64.VaesZ (load512_lane)
open VG.Spec.Gcm (Block blockAt mul)

/-! ## A load -/

/-- The lane-wise instructions of a load. -/
abbrev restZ (k : Nat) : List Instr :=
  [.zop (.zbin .vpshufb .xmm7 .xmm7 .xmm0)] ++
    (if k = 0 then [.zop (.zbin .vpxord .xmm7 .xmm7 .xmm2)] else []) ++ acc .xmm7 .xmm12

theorem ghLoad_eq (k : Nat) :
    ghLoad k = .vmovdqu32Load .xmm12 (at_ .r11 (64 * k)) :: .vmovdqu32Load .xmm7 (at_ .rdx (64 * k)) :: restZ k := by
  simp only [ghLoad, restZ, List.cons_append]

theorem lane_ld {k : Nat} (hk : k < 4) :
    zlaneSseBlock (restZ k) = some (ldacc (decide (k = 0)) .xmm12) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- Lane `l` of a 64-byte load into `d`. -/
theorem zlane_load (s : State) (d : XReg) (a : Addr) {l : Nat} (hl : l < 4) :
    (s.setZ d ((s.mem.readW a 512).extractLsb' 0 128) ((s.mem.readW a 512).extractLsb' 128 128)
      ((s.mem.readW a 512).extractLsb' 256 128) ((s.mem.readW a 512).extractLsb' 384 128)).zlane d l =
      s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
  simp only [ite_true]
  rw [pick4_lanes (fun i => (s.mem.readW a 512).extractLsb' (128 * i) 128) hl]
  exact load512_lane _ _ hl

/-- Four powers from `scratch + 64 k` into `zmm12`, and blocks `4k`–`4k + 3`
at `rdx + 64 k` added to the lanes' products with them. -/
theorem ghLoad_ok {k : Nat} (hk : k < 4) (t : State) (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((64 * k : Nat) : Int)) 64)
    (hpin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((64 * k : Nat) : Int)) 64) :
    WP isa (.block (ghLoad k)) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = (prod (t.zproj l)).acc
        ((if k = 0 then t.zlane .xmm2 l else 0) ^^^
          blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  let ap := t.gpr .r11 + BitVec.ofInt 64 ((64 * k : Nat) : Int)
  let ad := t.gpr .rdx + BitVec.ofInt 64 ((64 * k : Nat) : Int)
  let vp := t.mem.readW ap 512
  let t₁ := t.setZ .xmm12 (vp.extractLsb' 0 128) (vp.extractLsb' 128 128) (vp.extractLsb' 256 128)
    (vp.extractLsb' 384 128)
  let vd := t₁.mem.readW ad 512
  let t₂ := t₁.setZ .xmm7 (vd.extractLsb' 0 128) (vd.extractLsb' 128 128) (vd.extractLsb' 256 128)
    (vd.extractLsb' 384 128)
  rw [ghLoad_eq, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load512, ea_at, hpin, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₂, by simp only [isa, exec, State.load512, ea_at, t₁, State.setZ_gpr, State.setZ_rd, State.setZ_wr,
    State.setZ_mem, hin, ite_true, Option.map_some]; rfl, ?_⟩
  have keep : ∀ r, r ≠ .xmm12 → r ≠ .xmm7 → ∀ l < 4, t₂.zlane r l = t.zlane r l := fun r h12 h7 l hl => by
    simp only [t₂, t₁]
    rw [State.zlane_setZ_ne _ h7 _ _ _ _ hl, State.zlane_setZ_ne _ h12 _ _ _ _ hl]
  have l12 : ∀ l < 4, t₂.zlane .xmm12 l = t.mem.readW (ap + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    simp only [t₂]
    rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl]
    exact zlane_load t .xmm12 ap hl
  have l7 : ∀ l < 4, t₂.zlane .xmm7 l = t.mem.readW (ad + BitVec.ofNat 64 (16 * l)) 128 := fun l hl =>
    zlane_load t₁ .xmm7 ad hl
  refine WP.mono (WP.zlanes (lane_ld hk) fun l _ => ldacc_ok _ .xmm12 (t₂.zproj l) (by decide) (by decide)
    (by decide) (by decide) (by decide))
    fun t' ⟨hk', hq⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [(hq l hl).1]
    have hp : prod (t₂.zproj l) = prod (t.zproj l) := by
      simp only [prod, State.zproj_xmm, keep .xmm8 (by decide) (by decide) l hl,
        keep .xmm9 (by decide) (by decide) l hl, keep .xmm10 (by decide) (by decide) l hl]
    simp only [hp, State.zproj_xmm, l7 l hl, l12 l hl, keep .xmm0 (by decide) (by decide) l hl, h0 l hl,
      keep .xmm2 (by decide) (by decide) l hl]
    rw [← blockAt_eq]
    by_cases h : k = 0 <;> simp only [ad, ap, h, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  · refine ⟨hk'.gpr, hk'.mem, hk'.rd, hk'.wr, fun r hr l hl => ?_⟩
    have := (hq l hl).2.xmm r (fun h => hr (List.mem_cons_of_mem _ h))
    simp only [State.zproj_xmm] at this
    rw [this, keep r (fun h => hr (h ▸ List.mem_cons_self))
      (fun h => hr (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)) l hl]

/-! ## The reduction -/

/-- Lanes 2 and 3 of `r` added to lanes 0 and 1 (`VEX.256`, which clears the
upper lanes), through `zmm11`. -/
theorem fold1_ok (r : XReg) (h11 : r ≠ .xmm11) (s : State) :
    WP isa (.block [.zop (.vshufi32x4 .xmm11 r r 0x0e), .vop (.vbin .vpxor .l256 r r .xmm11)]) s fun s' =>
      (∀ l < 2, s'.lane r l = s.zlane r l ^^^ s.zlane r (l + 2)) ∧ ZFrame [.xmm11, r] s s' := by
  refine WP.zframe (by simp [vecDst, VOp.dst?, ZOp.dst]) ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil fun l hl => ?_⟩
  simp only [lane_vbin256, ite_true, VBinOp.sse, VG.Proof.Aes.X86_64.AesNi.eval_pxor]
  rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, zlane_vshufi32x4 _ _ _ _ _ _ (by omega),
    zlane_vshufi32x4 _ _ _ _ _ _ (by omega)]
  simp only [h11, ite_false, ite_true, shuf4Lanes]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

theorem fold_ok (s : State) :
    WP isa (.block foldLanes) s fun s' =>
      (∀ l < 2, prod (s'.proj l) = (prod (s.zproj l)).xor (prod (s.zproj (l + 2)))) ∧
      ZFrame [.xmm11, .xmm8, .xmm11, .xmm9, .xmm11, .xmm10] s s' := by
  rw [show foldLanes = [.zop (.vshufi32x4 .xmm11 .xmm8 .xmm8 0x0e), .vop (.vbin .vpxor .l256 .xmm8 .xmm8 .xmm11)] ++
    ([.zop (.vshufi32x4 .xmm11 .xmm9 .xmm9 0x0e), .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm11)] ++
    [.zop (.vshufi32x4 .xmm11 .xmm10 .xmm10 0x0e), .vop (.vbin .vpxor .l256 .xmm10 .xmm10 .xmm11)]) from rfl,
    WP.block_append_iff]
  refine WP.mono (fold1_ok .xmm8 (by decide) s) fun s₁ ⟨e₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fold1_ok .xmm9 (by decide) s₁) fun s₂ ⟨e₂, f₂⟩ => ?_
  refine WP.mono (fold1_ok .xmm10 (by decide) s₂) fun s' ⟨e', f'⟩ => ⟨fun l hl => ?_, f₁.comp (f₂.comp f')⟩
  have k8 : s'.lane .xmm8 l = s₁.lane .xmm8 l := by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, f'.zlane _ (by decide) l (by omega),
      f₂.zlane _ (by decide) l (by omega)]
  have k9 : s'.lane .xmm9 l = s₂.lane .xmm9 l := by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, f'.zlane _ (by decide) l (by omega)]
  have z9 : ∀ i < 4, s₁.zlane .xmm9 i = s.zlane .xmm9 i := fun i hi => f₁.zlane _ (by decide) i hi
  have z10 : ∀ i < 4, s₂.zlane .xmm10 i = s.zlane .xmm10 i := fun i hi => by
    rw [f₂.zlane _ (by decide) i hi, f₁.zlane _ (by decide) i hi]
  simp only [prod, State.proj_xmm, State.zproj_xmm, Prod.xor, k8, k9, e₁ l hl, e₂ l hl, e' l hl,
    z9 l (by omega), z9 (l + 2) (by omega), z10 l (by omega), z10 (l + 2) (by omega)]

/-- The two lanes' blocks added into `xmm2` (`VEX.128`, so lanes 1–3 are
cleared). -/
theorem combineZ_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.Vpclmul.combine) s fun s' =>
      s'.zlane .xmm2 0 = s.lane .xmm7 0 ^^^ s.lane .xmm7 1 ∧ (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      ZFrame [.xmm11, .xmm2] s s' := by
  refine WP.mono (WP.zframe (is := Impl.Gcm.X86_64.Vpclmul.combine) (rs := [.xmm11, .xmm2]) (by decide)
    (Q := fun s' => s'.zlane .xmm2 0 = s.lane .xmm7 0 ^^^ s.lane .xmm7 1 ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0)) ?_) fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rw [Impl.Gcm.X86_64.Vpclmul.combine, WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨?_, fun l hl1 hl4 => ?_⟩⟩
  · simp [VBinOp.sse, VG.Proof.Gcm.X86_64.Pclmul.eval_pxor, VOp.exec, State.setV, State.zlane, State.lane]
  · simp only [VOp.exec]
    rw [State.zlane_setV128 _ _ _ _ _ hl4]
    simp [show l ≠ 0 by omega]

/-! ## The products of a group -/

/-- The input of the `k`-th load in lane `l`: block `4k + l`, with `Y` (`yl l`)
added to block 0. -/
def inp (X : Nat → Block) (yl : Nat → Block) (k l : Nat) : Block := (if k = 0 then yl l else 0) ^^^ X (4 * k + l)

/-- The products of lane `l` after the first `n` loads, in the order `ord`. -/
def accN (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (l n : Nat) : Prod :=
  (List.range n).foldl (fun p i => p.acc (inp X yl (ord i) l) (P (ord i) l)) Prod.zero

theorem accN_succ (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (l n : Nat) :
    accN X P yl l (n + 1) = (accN X P yl l n).acc (inp X yl (ord n) l) (P (ord n) l) := by
  simp only [accN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `Y` after a group: the four lanes' products, lanes 2 and 3 added to 0
and 1, reduced and added. -/
abbrev yNew (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) : Block :=
  reduce ((accN X P yl 0 4).xor (accN X P yl 2 4)) ^^^ reduce ((accN X P yl 1 4).xor (accN X P yl 3 4))

theorem val_xor (p q : Prod) : (p.xor q).val = p.val + q.val := by
  simp only [Prod.val, Prod.xor, φ_xor]; ring

/-- Sixteen blocks, in `Q`, the products in the lanes and order of a group. -/
theorem step16Z (H Y X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ X₁₁ X₁₂ X₁₃ X₁₄ X₁₅ T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ T₁₀ T₁₁ T₁₂ T₁₃ T₁₄ T₁₅ T₁₆ : Block)
    (h₁ : x * φ T₁ = φ H) (h₂ : x * φ T₂ = φ H ^ 2) (h₃ : x * φ T₃ = φ H ^ 3) (h₄ : x * φ T₄ = φ H ^ 4) (h₅ : x * φ T₅ = φ H ^ 5) (h₆ : x * φ T₆ = φ H ^ 6) (h₇ : x * φ T₇ = φ H ^ 7) (h₈ : x * φ T₈ = φ H ^ 8) (h₉ : x * φ T₉ = φ H ^ 9) (h₁₀ : x * φ T₁₀ = φ H ^ 10) (h₁₁ : x * φ T₁₁ = φ H ^ 11) (h₁₂ : x * φ T₁₂ = φ H ^ 12) (h₁₃ : x * φ T₁₃ = φ H ^ 13) (h₁₄ : x * φ T₁₄ = φ H ^ 14) (h₁₅ : x * φ T₁₅ = φ H ^ 15) (h₁₆ : x * φ T₁₆ = φ H ^ 16) :
    reduce (((((Prod.zero.acc X₄ T₁₂).acc X₈ T₈).acc X₁₂ T₄).acc (Y ^^^ X₀) T₁₆).xor
        ((((Prod.zero.acc X₆ T₁₀).acc X₁₀ T₆).acc X₁₄ T₂).acc X₂ T₁₄)) ^^^
      reduce (((((Prod.zero.acc X₅ T₁₁).acc X₉ T₇).acc X₁₃ T₃).acc X₁ T₁₅).xor
        ((((Prod.zero.acc X₇ T₉).acc X₁₁ T₅).acc X₁₅ T₁).acc X₃ T₁₃)) =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((Y ^^^ X₀)) H ^^^ X₁) H ^^^ X₂) H ^^^ X₃) H ^^^ X₄) H ^^^ X₅) H ^^^ X₆) H ^^^ X₇) H ^^^ X₈) H ^^^ X₉) H ^^^ X₁₀) H ^^^ X₁₁) H ^^^ X₁₂) H ^^^ X₁₃) H ^^^ X₁₄) H ^^^ X₁₅) H := by
  apply φ_inj
  simp only [φ_xor, φ_reduce, val_xor, Prod.val_acc, Prod.val_zero, φ_mul]
  linear_combination (φ Y + φ X₀) * h₁₆ + φ X₁ * h₁₅ + φ X₂ * h₁₄ + φ X₃ * h₁₃ + φ X₄ * h₁₂ + φ X₅ * h₁₁ + φ X₆ * h₁₀ + φ X₇ * h₉ + φ X₈ * h₈ + φ X₉ * h₇ + φ X₁₀ * h₆ + φ X₁₁ * h₅ + φ X₁₂ * h₄ + φ X₁₃ * h₃ + φ X₁₄ * h₂ + φ X₁₅ * h₁

/-- The four lanes' products of a group, added and reduced: `GHASH` over the
sixteen blocks. -/
theorem finZ (H : Block) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block)
    (hy : ∀ l, 1 ≤ l → l < 4 → yl l = 0)
    (hP : ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ H ^ (16 - 4 * k - l)) :
    yNew X P yl =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((yl 0 ^^^ X 0)) H ^^^ X 1) H ^^^ X 2) H ^^^ X 3) H ^^^ X 4) H ^^^ X 5) H ^^^ X 6) H ^^^ X 7) H ^^^ X 8) H ^^^ X 9) H ^^^ X 10) H ^^^ X 11) H ^^^ X 12) H ^^^ X 13) H ^^^ X 14) H ^^^ X 15) H := by
  have h₁ := hP 3 (by decide) 3 (by decide)
  rw [show 16 - 4 * 3 - 3 = 1 from rfl, pow_one] at h₁
  have h₂ := hP 3 (by decide) 2 (by decide)
  have h₃ := hP 3 (by decide) 1 (by decide)
  have h₄ := hP 3 (by decide) 0 (by decide)
  have h₅ := hP 2 (by decide) 3 (by decide)
  have h₆ := hP 2 (by decide) 2 (by decide)
  have h₇ := hP 2 (by decide) 1 (by decide)
  have h₈ := hP 2 (by decide) 0 (by decide)
  have h₉ := hP 1 (by decide) 3 (by decide)
  have h₁₀ := hP 1 (by decide) 2 (by decide)
  have h₁₁ := hP 1 (by decide) 1 (by decide)
  have h₁₂ := hP 1 (by decide) 0 (by decide)
  have h₁₃ := hP 0 (by decide) 3 (by decide)
  have h₁₄ := hP 0 (by decide) 2 (by decide)
  have h₁₅ := hP 0 (by decide) 1 (by decide)
  have h₁₆ := hP 0 (by decide) 0 (by decide)
  simp only [Nat.reduceMul, Nat.reduceSub] at h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆
  simp only [yNew, accN, List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, ord, inp, hy 1 (by decide) (by decide), hy 2 (by decide) (by decide),
    hy 3 (by decide) (by decide), ↓reduceIte, Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero, zero_xor_b]
  exact step16Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆

/-! ## Hashing a group between the rounds -/

structure GEnv (s₀ : State) (lo : Nat) (a : Addr) (X : Nat → Block) (P : Nat → Nat → Block) (s : State) :
    Prop where
  rdx : s.gpr .rdx = a
  r11 : s.gpr .r11 = pp s₀
  xs : ∀ i, lo ≤ i → i < 16 → blockAt s.mem (a + BitVec.ofNat 64 (16 * i)) = X i
  pv : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  ina : ∀ k < 4, InRegions (s.rd ++ s.wr) (a + BitVec.ofInt 64 ((64 * k : Nat) : Int)) 64
  inp : ∀ k < 4, InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofInt 64 ((64 * k : Nat) : Int)) 64
  m0 : ∀ l < 4, s.zlane .xmm0 l = revMask

theorem GEnv.mono {s₀ : State} {lo lo' : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {s : State} (h : GEnv s₀ lo a X P s) (hl : lo ≤ lo') : GEnv s₀ lo' a X P s :=
  { h with xs := fun i hi hi' => h.xs i (Nat.le_trans hl hi) hi' }

theorem GEnv.zframe {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {s s' : State} {rs : List XReg} (h : GEnv s₀ lo a X P s) (f : ZFrame rs s s') (h0 : .xmm0 ∉ rs) :
    GEnv s₀ lo a X P s' :=
  ⟨by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.r11, fun i hi hi' => by rw [f.mem]; exact h.xs i hi hi',
    fun k hk l hl => by rw [f.mem]; exact h.pv k hk l hl, fun k hk => by rw [f.rd, f.wr]; exact h.ina k hk,
    fun k hk => by rw [f.rd, f.wr]; exact h.inp k hk, fun l hl => by rw [f.zlane _ h0 l hl]; exact h.m0 l hl⟩

theorem off4 (a : Addr) (k l : Nat) :
    a + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l) =
      a + BitVec.ofNat 64 (16 * (4 * k + l)) := by
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 64 * k + 16 * l = 16 * (4 * k + l) by omega]

theorem offp4 (a : Addr) (k l : Nat) :
    a + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l) =
      a + BitVec.ofNat 64 (64 * k + 16 * l) := by
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ord_lt (n : Nat) : ord n < 4 := by
  unfold ord; split <;> decide

/-- One GHASH load, the `n`-th. -/
theorem ghStep {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {yl : Nat → Block} {n : Nat} (hlo : lo ≤ 4 * ord n) {s : State}
    (hE : GEnv s₀ lo a X P s) (hp : ∀ l < 4, prod (s.zproj l) = accN X P yl l n)
    (hy : ∀ l < 4, s.zlane .xmm2 l = yl l) :
    WP isa (.block (ghLoad (ord n))) s fun s' => GEnv s₀ lo a X P s' ∧
      (∀ l < 4, prod (s'.zproj l) = accN X P yl l (n + 1)) ∧ (∀ l < 4, s'.zlane .xmm2 l = yl l) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  have hk := ord_lt n
  refine WP.mono (ghLoad_ok hk s hE.m0 (by rw [hE.rdx]; exact hE.ina _ hk) (by rw [hE.r11]; exact hE.inp _ hk))
    fun s' ⟨p', f'⟩ => ⟨hE.zframe f' (by decide), fun l hl => ?_, fun l hl => ?_, f'⟩
  · rw [p' l hl, hp l hl, accN_succ, hE.rdx, hE.r11, off4, offp4, hE.xs _ (by omega) (by omega),
      hE.pv _ hk l hl, hy l hl]
    rfl
  · rw [f'.zlane _ (by decide) l hl, hy l hl]

/-- The four lanes added into two, reduced, and added into `xmm2`. -/
theorem ghFin {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block} {s : State}
    (hE : GEnv s₀ lo a X P s) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block fin) s fun s' =>
      GEnv s₀ lo a X P s' ∧ s'.zlane .xmm2 0 =
        reduce ((prod (s.zproj 0)).xor (prod (s.zproj 2))) ^^^ reduce ((prod (s.zproj 1)).xor (prod (s.zproj 3))) ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      ZFrame [.xmm11, .xmm8, .xmm11, .xmm9, .xmm11, .xmm10, .xmm8, .xmm9, .xmm10, .xmm11, .xmm7, .xmm11, .xmm2]
        s s' := by
  rw [fin, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fold_ok s) fun s₁ ⟨p₁, f₁⟩ => ?_
  have h1' : ∀ l < 2, s₁.lane .xmm1 l = poly := fun l hl => by
    rw [← State.zlane_lt2 _ _ hl, f₁.zlane _ (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact h1 l hl
  rw [WP.block_append_iff]
  refine WP.mono (WP.zframe (rs := [.xmm8, .xmm9, .xmm10, .xmm11, .xmm7]) (by decide) (reduce_lanes s₁ h1'))
    fun s₂ ⟨⟨r₂, _⟩, f₂⟩ => ?_
  refine WP.mono (combineZ_ok s₂) fun s' ⟨c', y', f'⟩ =>
    ⟨(hE.zframe f₁ (by decide)).zframe (f₂.comp f') (by decide), ?_, y', f₁.comp (f₂.comp f')⟩
  rw [c', r₂ 0 (by decide), r₂ 1 (by decide), p₁ 0 (by decide), p₁ 1 (by decide)]

/-! ## The GHASH work of a group -/

/-- What holds before the blocks after round `j` of a group's rounds. -/
def QG (s₀ : State) (lo : Nat → Nat) (a : Addr) (X : Nat → Block) (P : Nat → Nat → Block)
    (yl : Nat → Block) (j : Nat) (s : State) : Prop :=
  GEnv s₀ (lo j) a X P s ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
  (if 5 < j then s.zlane .xmm2 0 = yNew X P yl ∧ ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0
   else (∀ l < 4, prod (s.zproj l) = accN X P yl l (min (j - 1) 4)) ∧
     ∀ l < 4, s.zlane .xmm2 l = yl l)

/-- The registers the GHASH work writes. -/
abbrev gRegs : List XReg := [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2]

theorem gRegs_ok : ∀ r ∈ gRegs, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

theorem QG.zframe {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {yl : Nat → Block} {j : Nat} {s s' : State} {rs : List XReg}
    (h : QG s₀ lo a X P yl j s) (f : ZFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∉ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg)) :
    QG s₀ lo a X P yl j s' := by
  obtain ⟨hE, h1, h2⟩ := h
  have k : ∀ r ∈ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), ∀ l < 4, s'.zlane r l = s.zlane r l :=
    fun r hr l hl => f.zlane r (fun h => hrs r h hr) l hl
  have kp : ∀ l < 4, prod (s'.zproj l) = prod (s.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, k .xmm8 (by decide) l hl, k .xmm9 (by decide) l hl,
      k .xmm10 (by decide) l hl]
  refine ⟨hE.zframe f (fun h => hrs _ h (by decide)), fun l hl => by
    rw [← State.zlane_lt2 _ _ hl, k .xmm1 (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact h1 l hl, ?_⟩
  split
  · rw [ite_t (by assumption)] at h2
    exact ⟨by rw [k .xmm2 (by decide) 0 (by decide)]; exact h2.1,
      fun l h1 h4 => by rw [k .xmm2 (by decide) l h4]; exact h2.2 l h1 h4⟩
  · rw [ite_f (by assumption)] at h2
    exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl, fun l hl => by rw [k .xmm2 (by decide) l hl]; exact h2.2 l hl⟩

/-- `batch_ok`'s obligation for the GHASH work between the rounds. -/
theorem gq_ok {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {yl : Nat → Block} (hmono : ∀ j, lo j ≤ lo (j + 1))
    (hrd : ∀ j, 1 ≤ j → j ≤ 4 → lo j ≤ 4 * ord (j - 1)) :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → QG s₀ lo a X P yl j s →
      WP isa (.block (gq j)) s fun s' => QG s₀ lo a X P yl (j + 1) s' ∧ ZFrame gRegs s s' := by
  intro j hj1 hj9 s _ ⟨hE, h1, h2⟩
  by_cases hl4 : j ≤ 4
  · -- A load.
    have hlo := hrd j hj1 hl4
    rw [ite_f (by omega)] at h2
    simp only [gq, show 1 ≤ j ∧ j ≤ 4 from ⟨hj1, hl4⟩, and_self, ite_true]
    rw [show min (j - 1) 4 = j - 1 by omega] at h2
    refine WP.mono (ghStep hlo hE h2.1 h2.2) fun s' ⟨hE', p', y', f'⟩ =>
      ⟨⟨hE'.mono (hmono j), fun l hl => by
        rw [← State.zlane_lt2 _ _ hl, f'.zlane _ (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact h1 l hl,
        ?_⟩, f'.mono (by decide)⟩
    rw [ite_f (by omega), show min (j + 1 - 1) 4 = j - 1 + 1 by omega]
    exact ⟨p', y'⟩
  · by_cases h5 : j = 5
    · -- The reduction.
      subst h5
      rw [ite_f (by omega)] at h2
      simp only [gq, show ¬ (1 ≤ 5 ∧ 5 ≤ 4) by omega, ite_false, ite_true]
      refine WP.mono (ghFin hE h1) fun s' ⟨hE', y0, y1, f'⟩ =>
        ⟨⟨hE'.mono (hmono 5), fun l hl => by
          rw [← State.zlane_lt2 _ _ hl, f'.zlane _ (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact h1 l hl,
          ?_⟩, f'.mono (by decide)⟩
      rw [ite_t (by omega)]
      refine ⟨by rw [y0, h2.1 0 (by decide), h2.1 1 (by decide), h2.1 2 (by decide), h2.1 3 (by decide)]; rfl, y1⟩
    · -- Nothing.
      have hg : gq j = [] := by
        simp only [gq, show ¬ (1 ≤ j ∧ j ≤ 4) by omega, ite_false, h5]
      rw [hg]
      refine WP.block_nil ⟨⟨hE.mono (hmono j), h1, ?_⟩, ZFrame.refl _ _⟩
      rw [ite_t (by omega)]
      rw [ite_t (by omega)] at h2
      exact h2

end VG.Proof.Gcm.X86_64.StitchZ
