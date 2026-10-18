module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Vec
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.VPack

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, sampling

The setup of the loop on seed `k`'s buffer loads the constants of the vector
code from the table (`setup_ok` for the first 168 iterations, from no
coefficients, `contSetup_ok` for the 112 more, from those kept), and the
loop runs groups of four iterations of `SampleNTT`'s loop on the buffer, to
polynomial `k` (`vgrp_ok`): with the vector code while there are fewer than
249 coefficients (`vec_ok`), and otherwise four iterations of
`vg_mlkem_sample_ntt`'s loop (`sca_ok`); `loop_ok` runs `8 N` of them.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.MlKem (xofByte sampleAfter)

/-! ## The constants -/

/-- 16 bytes as two quadwords. -/
theorem readW128_q (m : Mem) (a : Addr) : m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  have e1 := readW_extract m a (w := 128) (k := 8) (n := 8) (by bdd_omega)
  have e0 := readW_extract m a (w := 128) (k := 0) (n := 8) (by bdd_omega)
  rw [add_ofNat_zero] at e0
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < 64
  · rw [itT h, ← e0]; simp only [BitVec.getLsbD_extractLsb', h, decide_true, Bool.true_and]
    exact congrArg _ (by bdd_omega)
  · rw [itF h, ← e1]; simp only [BitVec.getLsbD_extractLsb', show j - 64 < 64 by bdd_omega, decide_true, Bool.true_and]
    exact congrArg _ (by bdd_omega)

/-- Lane `l` of constant `c`, from the table. -/
theorem cst_lane {σ : State} {m : Mem} (h : TabOK σ m) {c l : Nat} (hc : c < 6) (hl : l < 2) :
    (m.readW (at' σ (oTab + oCst + 32 * c)) 256).extractLsb' (128 * l) 128 =
      tabQ (256 + 4 * c + 2 * l + 1) ++ tabQ (256 + 4 * c + 2 * l) := by
  have a1 : at' σ (oTab + oCst + 32 * c) + BitVec.ofNat 64 (16 * l) + BitVec.ofNat 64 8 =
      at' σ (oTab + 8 * (256 + 4 * c + 2 * l + 1)) := by
    rw [at', Offset.add_add, Offset.add_add]; exact congrArg (fun x => scr σ + BitVec.ofNat 64 x) (by simp only [oCst]; omega)
  have a0 : at' σ (oTab + oCst + 32 * c) + BitVec.ofNat 64 (16 * l) = at' σ (oTab + 8 * (256 + 4 * c + 2 * l)) := by
    rw [at', Offset.add_add]; exact congrArg (fun x => scr σ + BitVec.ofNat 64 x) (by simp only [oCst]; omega)
  rw [show 128 * l = 8 * (16 * l) by bdd_omega, readW_extract _ _ (n := 16) (by bdd_omega), readW128_q, a1, a0,
    h _ (by bdd_omega), h _ (by bdd_omega)]

theorem cst_vals : (tabQ 257 ++ tabQ 256 = shuf 0 ∧ tabQ 259 ++ tabQ 258 = shuf 1) ∧
    (tabQ 261 ++ tabQ 260 = shV ∧ tabQ 263 ++ tabQ 262 = shV) ∧
    (tabQ 265 ++ tabQ 264 = maskV ∧ tabQ 267 ++ tabQ 266 = maskV) ∧
    (tabQ 269 ++ tabQ 268 = qV4 ∧ tabQ 271 ++ tabQ 270 = qV4) ∧
    (tabQ 273 ++ tabQ 272 = sgn 0 ∧ tabQ 275 ++ tabQ 274 = sgn 1) ∧
    (tabQ 277 ++ tabQ 276 = nib 0 ∧ tabQ 279 ++ tabQ 278 = nib 1) := by
  decide

/-- The table: the number of set bits of `m` in the high doubleword of
entry `m`, and their positions in the nibbles of the low one. -/
theorem tab_facts : ∀ m < 256, tabEntry m < 2 ^ 64 ∧ tabEntry m / 2 ^ 32 = (setBits m).length ∧
    ∀ i < (setBits m).length, tabEntry m % 2 ^ 32 / 16 ^ i % 8 = (setBits m).getD i 0 := by
  decide +kernel

theorem setBits_length (m : Nat) : (setBits m).length ≤ 8 := by
  unfold setBits; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-! ## The loop -/

/-- The coefficients only grow. -/
theorem Lt_mono (σ : State) (K t : Nat) : ∀ u, (Lt σ K t).length ≤ (Lt σ K (t + u)).length
  | 0 => Nat.le_refl _
  | u + 1 => Nat.le_trans (Lt_mono σ K t u) (by
      simp only [Lt]
      rw [← Nat.add_assoc, sampleAfter_succ]
      exact (Proof.MlKem.sampleStepCap_prefix _ _ _ _).length_le)

/-- At iteration `b + t` of the loop on seed `K`: the constants are in place
while there are fewer than 249 coefficients. -/
structure LVW (w16 : Bool) (σ s₀ : State) (K b t : Nat) (s : State) : Prop where
  lat : LAtW w16 σ s₀ K b t s
  vc : (Lt σ K (b + t)).length < 249 → VC s

/-- `LVW` with 32-bit coefficients. -/
abbrev LV := LVW false

theorem setup_eq (K : Nat) (w16 : Bool) : setup K w16 = [.mov .rsi (.reg .rbx),
    .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))), .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13),
    .alu .add .rbp (.imm (BitVec.ofNat 32 (pBytes w16 * K))), .mov32 .r10 (.imm 21)] := rfl

theorem contSetup_eq (K : Nat) (w16 : Bool) : contSetup K w16 = [.mov .rsi (.reg .rbx),
    .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))), .mov .rdi (.mem (at_ .rbx (oCnt + 8 * K))),
    .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (pBytes w16 * K))), .mov32 .r10 (.imm 14)] := rfl

theorem cstLoad_eq : cstLoad = [.vmovdquLoad .l256 .xmm8 (at_ .rbx (oTab + oCst + 32 * 0)),
    .vmovdquLoad .l256 .xmm9 (at_ .rbx (oTab + oCst + 32 * 1)), .vmovdquLoad .l256 .xmm10 (at_ .rbx (oTab + oCst + 32 * 2)),
    .vmovdquLoad .l256 .xmm11 (at_ .rbx (oTab + oCst + 32 * 3)), .vmovdquLoad .l256 .xmm12 (at_ .rbx (oTab + oCst + 32 * 4)),
    .vmovdquLoad .l256 .xmm13 (at_ .rbx (oTab + oCst + 32 * 5))] := rfl

section
variable {σ : State} (hp : PreW w16 σ)
include hp

/-- The constants of the vector code, from the table. -/
theorem cst_ok {s₀ : State} {K b t : Nat} {s : State} (l₁ : LAtW w16 σ s₀ K b t s) :
    WP isa (.block cstLoad) s fun s' => LVW w16 σ s₀ K b t s' ∧ s'.gpr .r10 = s.gpr .r10 := by
  have hbx : s.gpr .rbx = scr σ := l₁.lb.env.rbx
  have hin : ∀ c < 6, InRegions (s.rd ++ s.wr) (at' σ (oTab + oCst + 32 * c)) 32 := fun c hc =>
    in_scr' hp l₁.lb.env.rd l₁.lb.env.wr (by simp only [oTab, oCst]; omega)
  have tab := l₁.lb.tab
  rw [cstLoad_eq]
  refine wp_vld256 (by rw [ea_at, hbx]) (hin 0 (by decide)) fun s₂ u₂ =>
    wp_vld256 (by rw [ea_at, u₂.gpr, hbx]) (by rw [u₂.rd, u₂.wr]; exact hin 1 (by decide)) fun s₃ u₃ =>
    wp_vld256 (by rw [ea_at, u₃.gpr, u₂.gpr, hbx]) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin 2 (by decide))
      fun s₄ u₄ =>
    wp_vld256 (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, hbx])
      (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin 3 (by decide)) fun s₅ u₅ =>
    wp_vld256 (by rw [ea_at, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, hbx])
      (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin 4 (by decide)) fun s₆ u₆ =>
    wp_vld256 (by rw [ea_at, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, hbx])
      (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin 5 (by decide))
      fun s₇ u₇ => WP.block_nil ?_
  have g : s₇.gpr = s.gpr := by rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have m : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain ⟨⟨c0, c1⟩, ⟨c2, c3⟩, ⟨c4, c5⟩, ⟨c6, c7⟩, ⟨c8, c9⟩, ⟨c10, c11⟩⟩ := cst_vals
  have cl : ∀ c < 6, ∀ l < 2, (s.mem.readW (at' σ (oTab + oCst + 32 * c)) 256).extractLsb' (128 * l) 128 =
      tabQ (256 + 4 * c + 2 * l + 1) ++ tabQ (256 + 4 * c + 2 * l) := fun c hc l hl => cst_lane tab hc hl
  refine ⟨⟨l₁.same g m (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]),
    fun _ => ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩⟩,
    by rw [g]⟩
  · rw [u₇.other _ (by decide) l hl, u₆.other _ (by decide) l hl, u₅.other _ (by decide) l hl,
      u₄.other _ (by decide) l hl, u₃.other _ (by decide) l hl, u₂.val l hl, cl 0 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c0, c1]
  · rw [u₇.other _ (by decide) l hl, u₆.other _ (by decide) l hl, u₅.other _ (by decide) l hl,
      u₄.other _ (by decide) l hl, u₃.val l hl, u₂.mem, cl 1 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c2, c3]
  · rw [u₇.other _ (by decide) l hl, u₆.other _ (by decide) l hl, u₅.other _ (by decide) l hl,
      u₄.val l hl, u₃.mem, u₂.mem, cl 2 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c4, c5]
  · rw [u₇.other _ (by decide) l hl, u₆.other _ (by decide) l hl, u₅.val l hl, u₄.mem, u₃.mem, u₂.mem,
      cl 3 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c6, c7]
  · rw [u₇.other _ (by decide) l hl, u₆.val l hl, u₅.mem, u₄.mem, u₃.mem, u₂.mem, cl 4 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c8, c9]
  · rw [u₇.val l hl, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, cl 5 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c10, c11]

/-- The setup of the first 168 iterations on seed `K`, from `LBW w16 σ s K 0`. -/
theorem setup_ok {K : Nat} (hK : K < 4) {s : State} (h : LBW w16 σ s K 0 s) :
    WP isa (.block (setup K w16 ++ cstLoad)) s fun s' => LVW w16 σ s K 0 0 s' ∧ s'.gpr .r10 = BitVec.ofNat 64 21 := by
  rw [WP.block_append_iff, setup_eq]
  refine WP.mono (WP.keep [.rsi, .rdi, .rbp, .r10] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ (oBuf + 504 * K) ∧ s'.gpr .rdi = 0 ∧ s'.gpr .rbp = poly4W w16 (aP σ) K ∧
      s'.gpr .r10 = BitVec.ofNat 64 21)
    (by xrun [h.env.rbx, h.env.r13, sx_ofNat (show oBuf + 504 * K < 2 ^ 31 by simp only [oBuf]; omega),
      sx_ofNat (show pBytes w16 * K < 2 ^ 31 by wd_omega)]) rfl) fun s₁ ⟨⟨hm, hsi, hdi, hbp, h10⟩, k₁⟩ => ?_
  have l₁ : LAtW w16 σ s K 0 0 s₁ := ⟨h.keep hm k₁, by rw [hsi, Nat.mul_zero, add_ofNat_zero], by rw [hdi]; rfl,
    hbp, fun k hk => absurd hk (by simp [sampleAfter])⟩
  exact WP.mono (cst_ok hp l₁) fun s' ⟨h', h10'⟩ => ⟨h', by rw [h10', h10]⟩

/-- The setup of the 112 more iterations on seed `K`, from `LBW w16 σ s K 168`, with
the coefficients of the first 168 stored and their number kept. -/
theorem contSetup_ok {K : Nat} (hK : K < 4) {s : State} (h : LBW w16 σ s K 168 s)
    (hj : s.mem.readW (at' σ (oCnt + 8 * K)) 64 = BitVec.ofNat 64 (Lt σ K 168).length)
    (hst : Stored w16 s.mem (poly4W w16 (aP σ) K) (Lt σ K 168)) :
    WP isa (.block (contSetup K w16 ++ cstLoad)) s fun s' => LVW w16 σ s K 168 0 s' ∧ s'.gpr .r10 = BitVec.ofNat 64 14 := by
  have hin : InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oCnt + 8 * K)) 8 :=
    in_scr' hp h.env.rd h.env.wr (by simp only [oCnt]; omega)
  rw [WP.block_append_iff, contSetup_eq]
  refine WP.mono (WP.keep [.rsi, .rdi, .rbp, .r10] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ (oBuf + 504 * K) ∧ s'.gpr .rdi = BitVec.ofNat 64 (Lt σ K 168).length ∧
      s'.gpr .rbp = poly4W w16 (aP σ) K ∧ s'.gpr .r10 = BitVec.ofNat 64 14)
    (by
      xrun [h.env.rbx, h.env.r13, sx_ofNat (show oBuf + 504 * K < 2 ^ 31 by simp only [oBuf]; omega),
        sx_ofNat (show pBytes w16 * K < 2 ^ 31 by wd_omega), hin, hj]) rfl) fun s₁ ⟨⟨hm, hsi, hdi, hbp, h10⟩, k₁⟩ => ?_
  have l₁ : LAtW w16 σ s K 168 0 s₁ := ⟨h.keep hm k₁, by rw [hsi, Nat.mul_zero, add_ofNat_zero], hdi,
    hbp, by rw [hm]; exact hst⟩
  exact WP.mono (cst_ok hp l₁) fun s' ⟨h', h10'⟩ => ⟨h', by rw [h10', h10]⟩

/-- Four iterations of `vg_mlkem_sample_ntt`'s loop. -/
theorem sca_ok {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) (hbt : b + t + 4 ≤ 280) {s : State}
    (h : LAtW w16 σ s₀ K b t s) :
    WP isa (.seq (.block [.mov32 .rcx (.imm 4)]) (.loop (snBody w16) .ne)) s fun s' =>
      LAtW w16 σ s₀ K b (t + 4) s' ∧ s'.gpr .r10 = s.gpr .r10 :=
  wp_counted (N := 4) rfl (by decide) (fun u s' => LAtW w16 σ s₀ K b (t + u) s' ∧ s'.gpr .r10 = s.gpr .r10)
    (fun s' hm k => ⟨h.same' hm k, k.gpr (by decide)⟩)
    fun u hu s' ⟨hl, h10⟩ => WP.mono (WP.gpr (lat_step hp hK (by bdd_omega) (by bdd_omega) hl) (r := .r10) (by cases w16 <;> decide))
      fun s'' ⟨⟨hl', hc, hz⟩, h10'⟩ => ⟨⟨by rw [← Nat.add_assoc]; exact hl', h10'.trans h10⟩, hc, hz⟩

omit hp in
/-- The 12 bytes of the iterations `b + t` to `b + t + 3`. -/
theorem vbytes {s₀ : State} {K b t : Nat} (ht : t + 4 ≤ 168) (hbt : b + t + 4 ≤ 280) {s : State}
    (h : LAtW w16 σ s₀ K b t s) {i : Nat} (hi : i < 12) :
    (byte (s.mem.readW (s.gpr .rsi) 128) i).toNat = (xofByte (B σ K) (3 * (b + t) + i)).toNat := by
  rw [byte, byte_readW _ _ (by bdd_omega), out_byte h (by bdd_omega) (by bdd_omega)]

omit hp in
theorem vcand_eq {s₀ : State} {K b t : Nat} (ht : t + 4 ≤ 168) (hbt : b + t + 4 ≤ 280) {s : State}
    (h : LAtW w16 σ s₀ K b t s) {k : Nat} (hk : k < 8) :
    candN (fun i => (byte (s.mem.readW (s.gpr .rsi) 128) i).toNat) k = cand4 (xofByte (B σ K)) (3 * (b + t)) k := by
  unfold candN cand4 cb
  dsimp only
  rw [vbytes ht hbt h (i := 3 * (k / 2) + k % 2) (by bdd_omega),
    vbytes ht hbt h (i := 3 * (k / 2) + k % 2 + 1) (by bdd_omega)]
  split
  · rw [show 3 * (b + t) + (3 * (k / 2) + k % 2) = 3 * (b + t) + 3 * (k / 2) by bdd_omega,
      show 3 * (b + t) + (3 * (k / 2) + k % 2 + 1) = 3 * (b + t) + 3 * (k / 2) + 1 by bdd_omega]
  · rw [show 3 * (b + t) + (3 * (k / 2) + k % 2) = 3 * (b + t) + 3 * (k / 2) + 1 by bdd_omega,
      show 3 * (b + t) + (3 * (k / 2) + k % 2 + 1) = 3 * (b + t) + 3 * (k / 2) + 2 by bdd_omega]

/-- After the candidates and their mask, from iteration `b + t` with fewer than 249 coefficients. -/
structure VIW (w16 : Bool) (σ s₀ : State) (K b t : Nat) (s : State) : Prop where
  lat : LAtW w16 σ s₀ K b t s
  len : (Lt σ K (b + t)).length < 249
  vc : VC s
  rax : s.gpr .rax = BitVec.ofNat 64 (bsum (fun k => decide (cand4 (xofByte (B σ K)) (3 * (b + t)) k < 3329)) 8)
  cand : ∀ l < 2, s.lane .xmm0 l = candV (s.mem.readW (s.gpr .rsi) 128) l

/-- `VIW` with 32-bit coefficients. -/
abbrev VI := VIW false

/-- The candidates of the four iterations and their mask. -/
theorem vec1_ok {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) (hbt : b + t + 4 ≤ 280) {s : State}
    (h : LAtW w16 σ s₀ K b t s) (hv : VC s) (hl : (Lt σ K (b + t)).length < 249) :
    WP isa (.block vcand) s fun s' => VIW w16 σ s₀ K b t s' ∧ s'.gpr .r10 = s.gpr .r10 := by
  have hrsi : s.gpr .rsi = at' σ (oBuf + 504 * K + 3 * t) := by rw [h.rsi, at', at', Offset.add_add]
  have hin16 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16 := by
    rw [hrsi]; exact in_scr' hp h.lb.env.rd h.lb.env.wr (by simp only [oBuf]; omega)
  refine WP.mono (vcand_ok hv hin16) fun s₁ ⟨hax, h0, c₁, m₁, rd₁, wr₁, g₁⟩ => ?_
  have hM : maskN (fun i => (byte (s.mem.readW (s.gpr .rsi) 128) i).toNat) =
      bsum (fun k => decide (cand4 (xofByte (B σ K)) (3 * (b + t)) k < 3329)) 8 :=
    bsum_congr fun k hk => by rw [vcand_eq ht hbt h hk]
  refine ⟨⟨h.same' m₁ (rs := [.rax]) ⟨fun r hr => g₁ r (by simpa using hr), rd₁, wr₁⟩, hl, c₁, by rw [hax, hM],
    fun l hl' => by rw [h0 l hl', m₁, g₁ _ (by decide)]⟩, g₁ _ (by decide)⟩

/-- The candidates less than `q` to the polynomial, and `j` counting them. -/
theorem vec2_ok {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) (hbt : b + t + 4 ≤ 280) {s₁ : State}
    (hi : VIW w16 σ s₀ K b t s₁) :
    WP isa (.block (vput w16)) s₁ fun s' => LAtW w16 σ s₀ K b (t + 4) s' ∧ VC s' ∧ s'.gpr .r10 = s₁.gpr .r10 := by
  have h := hi.lat
  have c₁ := hi.vc
  have hl := hi.len
  have h0 := hi.cand
  have hax := hi.rax
  have hcand : ∀ k < 8, _ := fun k (hk : k < 8) => vcand_eq ht hbt h hk
  generalize hMd : bsum (fun k => decide (cand4 (xofByte (B σ K)) (3 * (b + t)) k < 3329)) 8 = M at hax
  have hM : M = bsum (fun k => decide (cand4 (xofByte (B σ K)) (3 * (b + t)) k < 3329)) 8 := hMd.symm
  have hM8 : M < 256 := by rw [hM]; exact bsum_lt _ 8
  have hsb : setBits M = (List.range 8).filter fun k => decide (cand4 (xofByte (B σ K)) (3 * (b + t)) k < 3329) := by
    rw [hM]; exact setBits_bsum _
  obtain ⟨hE, hcnt, hnib⟩ := tab_facts M hM8
  have htab : s₁.mem.readW (at' σ (oTab + 8 * M)) 64 = BitVec.ofNat 64 (tabEntry M) := by
    rw [h.lb.tab M (by bdd_omega), tabQ, ite_eq_left hM8]
  have hbx : s₁.gpr .rbx = scr σ := h.lb.env.rbx
  have hbp : s₁.gpr .rbp = poly4W w16 (aP σ) K := h.rbp
  have hlen : (Lt σ K (b + t)).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ (b + t)
  have hdi : (s₁.gpr .rdi).toNat = (Lt σ K (b + t)).length := by rw [h.rdi, ofNat64_toNat (by bdd_omega)]
  have haddr : s₁.gpr .rbp + BitVec.ofNat 64 (cw w16 / 8 * (s₁.gpr .rdi).toNat) =
      cAddr w16 (poly4W w16 (aP σ) K) (Lt σ K (b + t)).length := by
    rw [hbp, hdi]
  have hrd : s₁.rd ++ s₁.wr = [sdR σ, aR w16 σ, scrR σ] := regs hp h.lb.env
  have hin8 : (aR w16 σ).Contains (cAddr w16 (poly4W w16 (aP σ) K) (Lt σ K (b + t)).length) (8 * cw w16 / 8) := by
    rw [cAddr, poly4W, Offset.add_add]; exact Offset.contains_base _ (by wd_omega) (by wd_omega)
  have hout : InRegions s₁.wr (cAddr w16 (poly4W w16 (aP σ) K) (Lt σ K (b + t)).length) (cw w16) := by
    rw [h.lb.env.wr, hp.wr]
    exact ⟨aR w16 σ, by simp, by rw [show cw w16 = 8 * cw w16 / 8 by omega]; exact hin8⟩
  have hsep : ∀ V : BitVec (8 * cw w16), (s₁.mem.writeW (cAddr w16 (poly4W w16 (aP σ) K) (Lt σ K (b + t)).length)
      V).readW (at' σ (oTab + 8 * M + 4)) 32 = s₁.mem.readW (at' σ (oTab + 8 * M + 4)) 32 := fun V =>
    ((Frame.refl _ _).writeW (List.mem_singleton_self (aR w16 σ)) V hin8).readW
      (r := scrR σ) (Offset.contains_base _ (by simp only [oTab]; bdd_omega) (by simp only [oTab]; bdd_omega))
      (by simpa using hp.a_scr.symm) (by decide)
  refine WP.mono (vput_ok w16 c₁ h0 hax
    (by rw [hbx, hrd]; exact ⟨scrR σ, by simp, Offset.contains_base _ (by simp only [oTab]; bdd_omega)
      (by simp only [oTab]; bdd_omega)⟩)
    (by rw [hbx, hrd]; exact ⟨scrR σ, by simp, Offset.contains_base _ (by simp only [oTab]; bdd_omega)
      (by simp only [oTab]; bdd_omega)⟩)
    (by rw [haddr]; exact hout) (by rw [haddr, hbx]; exact hsep))
    fun s₂ ⟨⟨V, hm₂, hV⟩, hdi₂, hsi₂, c₂, rd₂, wr₂, g₂⟩ => ?_
  rw [hbx] at hV hdi₂
  rw [haddr] at hm₂
  -- the table's entry
  have hlo : (dword (s₁.mem.readW (scr σ + BitVec.ofNat 64 (oTab + 8 * M)) 128) 0).toNat = tabEntry M % 2 ^ 32 := by
    have e := readW_extract s₁.mem (scr σ + BitVec.ofNat 64 (oTab + 8 * M)) (w := 64) (k := 0) (n := 4) (by bdd_omega)
    rw [add_ofNat_zero] at e
    rw [dword_readW _ _ (by decide), Nat.mul_zero, add_ofNat_zero, ← e, ← at', htab, BitVec.extractLsb'_toNat,
      BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt hE]
  have hhi : (s₁.mem.readW (scr σ + BitVec.ofNat 64 (oTab + 8 * M + 4)) 32).toNat = (setBits M).length := by
    have e := readW_extract s₁.mem (scr σ + BitVec.ofNat 64 (oTab + 8 * M)) (w := 64) (k := 4) (n := 4) (by bdd_omega)
    rw [Offset.add_add] at e
    rw [← e, ← at', htab, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hE, hcnt]
    have := setBits_length M
    exact Nat.mod_eq_of_lt (by bdd_omega)
  -- the coefficients
  have hacc : acc4 (xofByte (B σ K)) (3 * (b + t)) =
      (setBits M).map fun k => ofNat (cand4 (xofByte (B σ K)) (3 * (b + t)) k) := by
    rw [acc4, hsb, q_eq]
  have hl' : (sampleAfter [] (xofByte (B σ K)) (b + t)).length < 249 := hl
  have hL4 : Lt σ K (b + (t + 4)) = Lt σ K (b + t) ++ acc4 (xofByte (B σ K)) (3 * (b + t)) := by
    rw [← Nat.add_assoc]; exact sampleAfter_four (by rw [n_eq]; omega)
  have hmem : ∀ k ∈ setBits M, k < 8 ∧ cand4 (xofByte (B σ K)) (3 * (b + t)) k < 3329 := fun k hk => by
    rw [hsb, List.mem_filter, List.mem_range, decide_eq_true_eq] at hk; exact hk
  have hst : Stored w16 s₂.mem (poly4W w16 (aP σ) K) (Lt σ K (b + (t + 4))) := by
    rw [hL4, hm₂]
    refine stored_write8 h.stored (by bdd_omega) (by rw [hacc, List.length_map]; exact setBits_length M) V fun i hi => ?_
    rw [hacc, List.length_map] at hi
    have hp' := hmem ((setBits M).getD i 0) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi)
    have hmap : ((setBits M).map fun k => ofNat (cand4 (xofByte (B σ K)) (3 * (b + t)) k)).getD i 0 =
        ofNat (cand4 (xofByte (B σ K)) (3 * (b + t)) ((setBits M).getD i 0)) := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
        Option.getD_some]
    rw [hV i (by have := setBits_length M; omega), hlo, hnib i hi, hcand _ hp'.1, hacc, hmap, ofNat,
      Fin.val_ofNat, Nat.mod_eq_of_lt (by rw [q_eq]; exact hp'.2)]
  have hf : Frame [cRegion w16 (poly4W w16 (aP σ) K)] s₁.mem s₂.mem := by
    rw [hm₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) V (Offset.contains_base _ (by wd_omega) (by wd_omega))
  have gk : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r := fun r _ h2 h3 => g₂ r h2 h3
  refine ⟨⟨h.lb.poly hp hK hf rd₂ wr₂ fun r hr => gk r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    ?_, ?_, by rw [gk _ (by decide) (by decide) (by decide), h.rbp], hst⟩, c₂, gk _ (by decide) (by decide) (by decide)⟩
  · rw [hsi₂, h.rsi, show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, Offset.add_add]
    exact congrArg (fun x => at' σ (oBuf + 504 * K) + BitVec.ofNat 64 x) (by bdd_omega)
  · rw [hdi₂, hL4, List.length_append, hacc, List.length_map]
    apply BitVec.eq_of_toNat_eq
    have := setBits_length M
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_setWidth, hdi, hhi, BitVec.toNat_ofNat]
    omega

theorem vec_ok {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) (hbt : b + t + 4 ≤ 280) {s : State}
    (h : LAtW w16 σ s₀ K b t s) (hv : VC s) (hl : (Lt σ K (b + t)).length < 249) :
    WP isa (.seq (.block vcand) (.block (vput w16))) s fun s' =>
      LAtW w16 σ s₀ K b (t + 4) s' ∧ VC s' ∧ s'.gpr .r10 = s.gpr .r10 :=
  WP.seq (WP.mono (vec1_ok hp hK ht hbt h hv hl) fun _ ⟨hi, h10⟩ =>
    WP.mono (vec2_ok hp hK ht hbt hi) fun _ ⟨l, c, h10'⟩ => ⟨l, c, h10'.trans h10⟩)

omit hp in
theorem cmp249_ok (s : State) :
    WP isa (.block [.alu .cmp .rdi (.imm 249)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .rdi).toNat < 249)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ x l, s'.lane x l = s.lane x l := by
  xrun [show BitVec.signExtend 64 (249 : BitVec 32) = 249 by decide, show (249 : BitVec 64).toNat = 249 from rfl]
  exact fun _ _ => rfl

omit hp in
theorem VC.same {s s' : State} (h : VC s) (hl : ∀ x l, s'.lane x l = s.lane x l) : VC s' :=
  ⟨fun l hl' => by rw [hl, h.c8 l hl'], fun l hl' => by rw [hl, h.c9 l hl'], fun l hl' => by rw [hl, h.c10 l hl'],
    fun l hl' => by rw [hl, h.c11 l hl'], fun l hl' => by rw [hl, h.c12 l hl'], fun l hl' => by rw [hl, h.c13 l hl']⟩

/-- Four iterations of the loop. -/
theorem vgrp_ok {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) (hbt : b + t + 4 ≤ 280) {s : State}
    (h : LVW w16 σ s₀ K b t s) :
    WP isa (vgrp w16) s fun s' => LVW w16 σ s₀ K b (t + 4) s' ∧ s'.gpr .r10 = s.gpr .r10 := by
  unfold vgrp
  refine WP.seq (WP.mono (cmp249_ok s) fun s₁ ⟨hcf, hm, hg, hrd, hwr, hl⟩ => ?_)
  have l₁ : LAtW w16 σ s₀ K b t s₁ := h.lat.same hg hm hrd hwr
  have hlen : (Lt σ K (b + t)).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ (b + t)
  rw [h.lat.rdi, ofNat64_toNat (by bdd_omega)] at hcf
  refine WP.ite _ hcf (fun hb => ?_) fun hb => ?_
  · have hb' : (Lt σ K (b + t)).length < 249 := of_decide_eq_true hb
    exact WP.mono (vec_ok hp hK ht hbt l₁ ((h.vc hb').same hl) hb') fun s' ⟨l', c', h10⟩ =>
      ⟨⟨l', fun _ => c'⟩, by rw [h10, hg]⟩
  · have hb' : ¬ (Lt σ K (b + t)).length < 249 := of_decide_eq_false hb
    exact WP.mono (sca_ok hp hK ht hbt l₁) fun s' ⟨l', h10⟩ =>
      ⟨⟨l', fun h' => absurd (Nat.lt_of_le_of_lt (Lt_mono σ K (b + t) 4) (by rwa [Nat.add_assoc])) hb'⟩,
        by rw [h10, hg]⟩

omit hp in
theorem sub10_ok (s : State) :
    WP isa (.block [.alu .sub .r10 (.imm 1)]) s fun s' => (s'.mem = s.mem ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.zf = some (s.gpr .r10 - 1 == 0) ∧ ∀ x l, s'.lane x l = s.lane x l) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun
  exact fun _ _ => rfl

/-- `N` iterations of the loop's body: `8 N` iterations of `SampleNTT`'s. -/
theorem loop_ok {s₀ : State} {K b N : Nat} (hK : K < 4) (hN : 0 < N) (hN' : 8 * N ≤ 168) (hbN : b + 8 * N ≤ 280)
    {s : State} (h : LVW w16 σ s₀ K b 0 s) (h10 : s.gpr .r10 = BitVec.ofNat 64 N) :
    WP isa (.loop (Sample4.vbody w16) .ne) s (LAtW w16 σ s₀ K b (8 * N)) := by
  refine wp_countdown (cnt := .r10) (N := N) (by bdd_omega) hN (fun i s => LVW w16 σ s₀ K b (8 * i) s)
    (fun i hi s hs _ => ?_) (fun _ h => h.lat) h h10
  unfold Sample4.vbody
  refine WP.seq (WP.mono (vgrp_ok hp hK (by bdd_omega) (by bdd_omega) hs) fun s₁ ⟨h₁, g₁⟩ =>
    WP.seq (WP.mono (vgrp_ok hp hK (by bdd_omega) (by bdd_omega) h₁) fun s₂ ⟨h₂, g₂⟩ =>
      WP.mono (sub10_ok s₂) fun s₃ ⟨⟨hm, h10', hz, hl⟩, k⟩ => ?_))
  have e : 8 * i + 4 + 4 = 8 * (i + 1) := by bdd_omega
  rw [e] at h₂
  exact ⟨⟨h₂.lat.same' hm k, fun h' => (h₂.vc h').same hl⟩, by rw [h10', g₂, g₁], by rw [hz, g₂, g₁]⟩

omit hp in
/-- `vzeroupper` changes no register or memory the invariants see. -/
theorem vz_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun s' => s'.mem = s.mem ∧ Keep [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left', Keep]
  exact ⟨rfl, fun _ _ => rfl, rfl, rfl⟩

end

end VG.Proof.MlKem.X86_64.S4
