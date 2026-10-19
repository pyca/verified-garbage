module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Wide
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, sampling

The setup of the loop on seed `k`'s buffer loads the constants of the vector
code from the table (`setup_ok` for the first 168 iterations, from no
coefficients, `contSetup_ok` for the 112 more, from those kept), and the
loop runs groups of eight iterations of `SampleNTT`'s loop on the buffer, to
polynomial `k` (`vgrp_ok`): for 16-bit coefficients with the vector code
while there are fewer than 241 coefficients (`vec_ok`: `vec1_ok` for
`vcand`, `vec2a_ok` and `vec2b_ok` for the two halves of `vput`), and
otherwise eight iterations of `vg_mlkem_sample_ntt`'s loop (`sca_ok`);
`loop_ok` runs `8 N` of them.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.MlKem (xofByte sampleAfter)

/-! ## The constants -/

theorem cst_vals : (consts.getD 1 0 ++ consts.getD 0 0 = shufW 0 ∧ consts.getD 3 0 ++ consts.getD 2 0 = shufW 1) ∧
    (consts.getD 5 0 ++ consts.getD 4 0 = fffW ∧ consts.getD 7 0 ++ consts.getD 6 0 = fffW) ∧
    (consts.getD 9 0 ++ consts.getD 8 0 = qW ∧ consts.getD 11 0 ++ consts.getD 10 0 = qW) := by
  decide

/-- Lane `l` of constant `c`, from the static. -/
theorem cst_lane {c l : Nat} (hc : c < 3) (hl : l < 2) :
    (if l = 0 then tblWords.getD (512 + 4 * c + 1) 0 ++ tblWords.getD (512 + 4 * c) 0
      else tblWords.getD (512 + 4 * c + 3) 0 ++ tblWords.getD (512 + 4 * c + 2) 0) =
      consts.getD (4 * c + 2 * l + 1) 0 ++ consts.getD (4 * c + 2 * l) 0 := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [ite_eq_left rfl, show 512 + 4 * c + 1 = 512 + (4 * c + 1) by omega, tblWords_cst (by omega),
      tblWords_cst (by omega)]
    simp only [Nat.mul_zero, Nat.add_zero]
  · rw [ite_eq_right (by decide), show 512 + 4 * c + 3 = 512 + (4 * c + 3) by omega,
      show 512 + 4 * c + 2 = 512 + (4 * c + 2) by omega, tblWords_cst (by omega), tblWords_cst (by omega)]

/-- Where the constants are in the static. -/
theorem cst_at {s : State} (ht : TabOK s) {c : Nat} (hc : c < 3) :
    (s.ea (at_ .r11 (oCst + 32 * c)) - s.syms tblName).toNat = 8 * (512 + 4 * c) := by
  rw [ea_at, show s.gpr .r11 = s.syms tblName from ht, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  simp only [oCst]; omega

/-! ## The loop -/

/-- The coefficients only grow. -/
theorem Lt_mono (σ : State) (K t : Nat) : ∀ u, (Lt σ K t).length ≤ (Lt σ K (t + u)).length
  | 0 => Nat.le_refl _
  | u + 1 => Nat.le_trans (Lt_mono σ K t u) (by
      simp only [Lt]
      rw [← Nat.add_assoc, sampleAfter_succ]
      exact (Proof.MlKem.sampleStepCap_prefix _ _ _ _).length_le)

/-- At iteration `b + t` of the loop on seed `K`: the constants are in place
for 16-bit coefficients while there are fewer than 241 coefficients. -/
structure LVW (w16 : Bool) (σ s₀ : State) (K b t : Nat) (s : State) : Prop where
  lat : LAtW w16 σ s₀ K b t s
  vc : w16 = true → (Lt σ K (b + t)).length < 241 → VC s

theorem setup_eq (K : Nat) (w16 : Bool) : setup K w16 = [.mov .rsi (.reg .rbx),
    .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))), .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13),
    .alu .add .rbp (.imm (BitVec.ofNat 32 (pBytes w16 * K))), .mov32 .r10 (.imm 21)] := rfl

theorem contSetup_eq (K : Nat) (w16 : Bool) : contSetup K w16 = [.mov .rsi (.reg .rbx),
    .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))), .mov .rdi (.mem (at_ .rbx (oCnt + 8 * K))),
    .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (pBytes w16 * K))), .mov32 .r10 (.imm 14)] := rfl

theorem cstLoad_eq : cstLoad = [.vmovdquTbl .xmm8 (at_ .r11 (oCst + 32 * 0)) tblName tblWords,
    .vmovdquTbl .xmm9 (at_ .r11 (oCst + 32 * 1)) tblName tblWords,
    .vmovdquTbl .xmm10 (at_ .r11 (oCst + 32 * 2)) tblName tblWords] := rfl

section
variable {σ : State} (hp : PreW w16 σ)
include hp

omit hp in
/-- The constants of the vector code, from the static. -/
theorem cst_ok {s₀ : State} {K b t : Nat} {s : State} (l₁ : LAtW w16 σ s₀ K b t s) :
    WP isa (.block cstLoad) s fun s' => LVW w16 σ s₀ K b t s' ∧ s'.gpr .r10 = s.gpr .r10 := by
  have tab := l₁.lb.tab
  have hl : ∀ c < 3, (512 + 4 * c) + 4 ≤ tblWords.length := fun c hc => by rw [tblWords_length]; omega
  rw [cstLoad_eq]
  refine wp_vtbl tab (cst_at tab (by decide)) (hl 0 (by decide)) fun s₂ u₂ =>
    have t₂ := tab.of (by rw [u₂.gpr]) u₂.syms
    wp_vtbl t₂ (cst_at t₂ (by decide)) (hl 1 (by decide)) fun s₃ u₃ =>
    have t₃ := t₂.of (by rw [u₃.gpr]) u₃.syms
    wp_vtbl t₃ (cst_at t₃ (by decide)) (hl 2 (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have g : s₄.gpr = s.gpr := by rw [u₄.gpr, u₃.gpr, u₂.gpr]
  have m : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  obtain ⟨⟨c0, c1⟩, ⟨c2, c3⟩, ⟨c4, c5⟩⟩ := cst_vals
  have cl : ∀ c < 3, ∀ l < 2, _ := fun c (hc : c < 3) l (hl : l < 2) => cst_lane hc hl
  refine ⟨⟨l₁.same g m (by rw [u₄.rd, u₃.rd, u₂.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr]) (by rw [u₄.syms, u₃.syms, u₂.syms]),
    fun _ _ => ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩⟩, by rw [g]⟩
  · rw [u₄.other _ (by decide) l hl, u₃.other _ (by decide) l hl, u₂.val l hl, cl 0 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c0, c1]
  · rw [u₄.other _ (by decide) l hl, u₃.val l hl, cl 1 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c2, c3]
  · rw [u₄.val l hl, cl 2 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c4, c5]

/-- The setup of the first 168 iterations on seed `K`, from `LBW w16 σ s K 0`. -/
theorem setup_ok {K : Nat} (hK : K < 4) {s : State} (h : LBW w16 σ s K 0 s) :
    WP isa (.block (setup K w16 ++ cstLoad)) s fun s' => LVW w16 σ s K 0 0 s' ∧ s'.gpr .r10 = BitVec.ofNat 64 21 := by
  rw [WP.block_append_iff, setup_eq]
  refine WP.mono_syms (WP.keep [.rsi, .rdi, .rbp, .r10] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ (oBuf + 504 * K) ∧ s'.gpr .rdi = 0 ∧ s'.gpr .rbp = poly4W w16 (aP σ) K ∧
      s'.gpr .r10 = BitVec.ofNat 64 21)
    (by xrun [h.env.rbx, h.env.r13, sx_ofNat (show oBuf + 504 * K < 2 ^ 31 by simp only [oBuf]; omega),
      sx_ofNat (show pBytes w16 * K < 2 ^ 31 by wd_omega)]) rfl) fun s₁ ⟨⟨hm, hsi, hdi, hbp, h10⟩, k₁⟩ sy => ?_
  have l₁ : LAtW w16 σ s K 0 0 s₁ := ⟨h.keep hm k₁ sy, by rw [hsi, Nat.mul_zero, add_ofNat_zero], by rw [hdi]; rfl,
    hbp, fun k hk => absurd hk (by simp [sampleAfter])⟩
  exact WP.mono (cst_ok l₁) fun s' ⟨h', h10'⟩ => ⟨h', by rw [h10', h10]⟩

/-- The setup of the 112 more iterations on seed `K`, from `LBW w16 σ s K 168`, with
the coefficients of the first 168 stored and their number kept. -/
theorem contSetup_ok {K : Nat} (hK : K < 4) {s : State} (h : LBW w16 σ s K 168 s)
    (hj : s.mem.readW (at' σ (oCnt + 8 * K)) 64 = BitVec.ofNat 64 (Lt σ K 168).length)
    (hst : Stored w16 s.mem (poly4W w16 (aP σ) K) (Lt σ K 168)) :
    WP isa (.block (contSetup K w16 ++ cstLoad)) s fun s' => LVW w16 σ s K 168 0 s' ∧ s'.gpr .r10 = BitVec.ofNat 64 14 := by
  have hin : InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oCnt + 8 * K)) 8 :=
    in_scr' hp h.env.rd h.env.wr (by simp only [oCnt]; omega)
  rw [WP.block_append_iff, contSetup_eq]
  refine WP.mono_syms (WP.keep [.rsi, .rdi, .rbp, .r10] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ (oBuf + 504 * K) ∧ s'.gpr .rdi = BitVec.ofNat 64 (Lt σ K 168).length ∧
      s'.gpr .rbp = poly4W w16 (aP σ) K ∧ s'.gpr .r10 = BitVec.ofNat 64 14)
    (by
      xrun [h.env.rbx, h.env.r13, sx_ofNat (show oBuf + 504 * K < 2 ^ 31 by simp only [oBuf]; omega),
        sx_ofNat (show pBytes w16 * K < 2 ^ 31 by wd_omega), hin, hj]) rfl) fun s₁ ⟨⟨hm, hsi, hdi, hbp, h10⟩, k₁⟩ sy => ?_
  have l₁ : LAtW w16 σ s K 168 0 s₁ := ⟨h.keep hm k₁ sy, by rw [hsi, Nat.mul_zero, add_ofNat_zero], hdi,
    hbp, by rw [hm]; exact hst⟩
  exact WP.mono (cst_ok l₁) fun s' ⟨h', h10'⟩ => ⟨h', by rw [h10', h10]⟩

/-- Eight iterations of `vg_mlkem_sample_ntt`'s loop. -/
theorem sca_ok {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 8 ≤ 168) (hbt : b + t + 8 ≤ 280) {s : State}
    (h : LAtW w16 σ s₀ K b t s) :
    WP isa (sca8 w16) s fun s' =>
      LAtW w16 σ s₀ K b (t + 8) s' ∧ s'.gpr .r10 = s.gpr .r10 :=
  WP.seq (WP.mono_syms (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 8)
      (by xrun) rfl) fun s₁ ⟨⟨hm, hc⟩, k⟩ sy =>
    wp_countdown (cnt := .rcx) (N := 8) (by decide) (by decide)
      (fun u s' => LAtW w16 σ s₀ K b (t + u) s' ∧ s'.gpr .r10 = s.gpr .r10 ∧ s'.syms = s.syms)
      (fun u hu s' ⟨hl, h10, hs⟩ _ => WP.mono_syms (WP.gpr (lat_step hp hK (by bdd_omega) (by bdd_omega) hl) (r := .r10)
        (by cases w16 <;> decide))
        fun s'' ⟨⟨hl', hc, hz⟩, h10'⟩ sy' => ⟨⟨by rw [← Nat.add_assoc]; exact hl', h10'.trans h10, sy'.trans hs⟩, hc, hz⟩)
      (fun _ h => ⟨h.1, h.2.1⟩) ⟨h.same' hm k sy, by rw [k.gpr (by decide)], sy⟩ hc)

omit hp in
/-- The 24 bytes of the iterations `b + t` to `b + t + 7`. -/
theorem vbytes {s₀ : State} {K b t : Nat} (ht : t + 8 ≤ 168) (hbt : b + t + 8 ≤ 280) {s : State}
    (h : LAtW w16 σ s₀ K b t s) {i : Nat} (hi : i < 24) :
    (byteY (s.mem.readW (s.gpr .rsi) 256) i).toNat = (xofByte (B σ K) (3 * (b + t) + i)).toNat := by
  rw [byteY, byte_readW _ _ (by bdd_omega), out_byte h (by bdd_omega) (by bdd_omega)]

omit hp in
/-- Candidate `k` of the 24 bytes, candidate `k % 8` of the four chunks of its half. -/
theorem vcand_eq {s₀ : State} {K b t : Nat} (ht : t + 8 ≤ 168) (hbt : b + t + 8 ≤ 280) {s : State}
    (h : LAtW w16 σ s₀ K b t s) {k : Nat} (hk : k < 16) :
    candN (fun i => (byteY (s.mem.readW (s.gpr .rsi) 256) i).toNat) k =
      cand4 (xofByte (B σ K)) (3 * (b + t) + 12 * (k / 8)) (k % 8) := by
  unfold candN cand4 cb
  dsimp only
  rw [vbytes ht hbt h (i := 3 * (k / 2) + k % 2) (by bdd_omega),
    vbytes ht hbt h (i := 3 * (k / 2) + k % 2 + 1) (by bdd_omega), show k % 8 % 2 = k % 2 by omega]
  have e : 3 * (b + t) + 12 * (k / 8) + 3 * (k % 8 / 2) = 3 * (b + t) + 3 * (k / 2) := by omega
  split
  · rw [show 3 * (b + t) + (3 * (k / 2) + k % 2) = 3 * (b + t) + 3 * (k / 2) by bdd_omega,
      show 3 * (b + t) + (3 * (k / 2) + k % 2 + 1) = 3 * (b + t) + 3 * (k / 2) + 1 by bdd_omega, e]
  · rw [show 3 * (b + t) + (3 * (k / 2) + k % 2) = 3 * (b + t) + 3 * (k / 2) + 1 by bdd_omega,
      show 3 * (b + t) + (3 * (k / 2) + k % 2 + 1) = 3 * (b + t) + 3 * (k / 2) + 2 by bdd_omega, e]

omit hp in
/-- The coefficients of the four chunks from byte `p` are those of the mask's bits. -/
theorem acc_mask {X : BitVec 256} {out : Nat → Byte} {p l : Nat}
    (hc : ∀ k < 8, candN (fun i => (byteY X i).toNat) (8 * l + k) = cand4 out p k) :
    acc4 out p = (setBits (maskL X l)).map fun k => ofNat (cand4 out p k) := by
  rw [acc4, maskL, setBits_bsum, q_eq]
  congr 1
  apply List.filter_congr
  intro k hk
  rw [hc k (List.mem_range.mp hk)]

omit hp in
/-- The words of a lane after the compaction are its coefficients. -/
theorem comp_words {X : BitVec 256} {out : Nat → Byte} {p l : Nat} (hl : l < 2)
    (hc : ∀ k < 8, candN (fun i => (byteY X i).toNat) (8 * l + k) = cand4 out p k) :
    ∀ i < (acc4 out p).length, ((compW X l).extractLsb' (cw true * i) (cw true)).toNat = ((acc4 out p).getD i 0).val := by
  intro i hi
  rw [acc_mask hc, List.length_map] at hi
  rw [acc_mask hc]
  have hs := setBits_lt hi
  have hq : cand4 out p ((setBits (maskL X l)).getD i 0) < q := by
    have hmem : (setBits (maskL X l)).getD i 0 ∈ setBits (maskL X l) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
    generalize (setBits (maskL X l)).getD i 0 = x at hmem ⊢
    rw [maskL, setBits_bsum, List.mem_filter, decide_eq_true_eq] at hmem
    rw [← hc _ (List.mem_range.mp hmem.1), q_eq]; exact hmem.2
  show (word (compW X l) i).toNat = _
  rw [compW, pshufb_idxV _ hi, cand_word X hl hs, hc _ hs]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
    Option.getD_some, ofNat, Fin.val_ofNat] at hq ⊢
  exact (Nat.mod_eq_of_lt hq).symm

omit hp in
/-- The mask of the candidates less than `q` of half `l` of the 24 bytes. -/
theorem maskL_eq {s₀ : State} {K b t : Nat} (ht : t + 8 ≤ 168) (hbt : b + t + 8 ≤ 280) {s : State}
    (h : LAtW w16 σ s₀ K b t s) {l : Nat} (hl : l < 2) :
    maskL (s.mem.readW (s.gpr .rsi) 256) l =
      bsum (fun i => decide (cand4 (xofByte (B σ K)) (3 * (b + t) + 12 * l) i < 3329)) 8 :=
  bsum_congr fun i hi => by
    rw [vcand_eq ht hbt h (by omega), show (8 * l + i) / 8 = l by omega, show (8 * l + i) % 8 = i by omega]

/-- `s₁` after `vcand` from `s`. -/
abbrev VIF (s s₁ : State) : Prop :=
    (s₁.gpr .rax).toNat = maskL (s.mem.readW (s.gpr .rsi) 256) 0 + 256 * maskL (s.mem.readW (s.gpr .rsi) 256) 0 +
      65536 * maskL (s.mem.readW (s.gpr .rsi) 256) 1 + 16777216 * maskL (s.mem.readW (s.gpr .rsi) 256) 1 ∧
    (∀ l < 2, s₁.lane .xmm0 l = candW (s.mem.readW (s.gpr .rsi) 256) l) ∧ VC s₁ ∧ s₁.mem = s.mem ∧
    s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.syms = s.syms ∧ ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r

/-- After `vcand`, at iteration `b + t` with fewer than 241 coefficients. -/
def VIW (w16 : Bool) (σ s₀ : State) (K b t : Nat) (s₁ : State) : Prop :=
  ∃ s, LAtW w16 σ s₀ K b t s ∧ (Lt σ K (b + t)).length < 241 ∧ VIF s s₁

/-- After `vcand` and `vputA`, at iteration `b + t` with fewer than 241 coefficients. -/
def VPW (w16 : Bool) (σ s₀ : State) (K b t : Nat) (s₂ : State) : Prop :=
  ∃ s s₁, LAtW w16 σ s₀ K b t s ∧ (Lt σ K (b + t)).length < 241 ∧ VIF s s₁ ∧
    VPA (s.mem.readW (s.gpr .rsi) 256) s₁ s₂

/-- The candidates of eight iterations and their mask. -/
theorem vec1_ok {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 8 ≤ 168) {s : State} (h : LAtW w16 σ s₀ K b t s)
    (hv : VC s) (hl : (Lt σ K (b + t)).length < 241) :
    WP isa (.block vcand) s fun s₁ => VIW w16 σ s₀ K b t s₁ ∧ s₁.gpr .r10 = s.gpr .r10 := by
  have hrsi : s.gpr .rsi = at' σ (oBuf + 504 * K + 3 * t) := by rw [h.rsi, at', at', Offset.add_add]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 32 := by
    rw [hrsi]; exact in_scr' hp h.lb.env.rd h.lb.env.wr (by simp only [oBuf]; omega)
  exact WP.mono (vcand_ok hv hin) fun s₁ h₁ => ⟨⟨s, h, hl, h₁⟩, h₁.2.2.2.2.2.2.2 _ (by decide)⟩

/-- The output region holds 8 coefficients from `n`. -/
theorem out_reg (hw : w16 = true) {s₀ : State} {K b t : Nat} (hK : K < 4) {s : State} (h : LAtW w16 σ s₀ K b t s)
    {s₁ : State} (wr₁ : s₁.wr = s.wr) {n : Nat} (hn : n + 8 ≤ 256) :
    InRegions s₁.wr (poly4W true (aP σ) K + BitVec.ofNat 64 (2 * n)) 16 := by
  subst hw
  rw [wr₁, h.lb.env.wr, hp.wr]
  exact ⟨aRW true σ, by simp, by
    rw [poly4W, Offset.add_add]; exact Offset.contains_base _ (by simp only [pBytes, ↓reduceIte]; omega)
      (by simp only [pBytes, ↓reduceIte]; omega)⟩

/-- The low half's coefficients, after `vcand`. -/
theorem vec2a_ok (hw : w16 = true) {s₀ : State} {K b t : Nat} (hK : K < 4) {s₁ : State}
    (hi : VIW w16 σ s₀ K b t s₁) :
    WP isa (.block vputA) s₁ fun s₂ => VPW w16 σ s₀ K b t s₂ ∧ s₂.gpr .r10 = s₁.gpr .r10 := by
  subst hw
  obtain ⟨s, h, hl, hf⟩ := hi
  obtain ⟨hax, h0, c₁, -, -, wr₁, sy₁, g₁⟩ := id hf
  have hdi : (s₁.gpr .rdi).toNat = (Lt σ K (b + t)).length := by
    rw [g₁ _ (by decide), h.rdi, ofNat64_toNat (by omega)]
  have hbp : s₁.gpr .rbp = poly4W true (aP σ) K := by rw [g₁ _ (by decide), h.rbp]
  exact WP.mono (vputA_ok c₁ h0 hax (by rw [g₁ _ (by decide), sy₁]; exact h.lb.tab) (by rw [hdi]; omega)
    (by rw [hbp, hdi]; exact out_reg hp rfl hK h wr₁ (by omega)))
    fun s₂ hv => ⟨⟨s, s₁, h, hl, hf, hv⟩, hv.gpr _ (by decide) (by decide) (by decide)⟩

/-- The high half's coefficients, after `vputA`. -/
theorem vec2b_ok (hw : w16 = true) {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 8 ≤ 168)
    (hbt : b + t + 8 ≤ 280) {s₂ : State} (hi : VPW w16 σ s₀ K b t s₂) :
    WP isa (.block vputB) s₂ fun s' =>
      LAtW w16 σ s₀ K b (t + 8) s' ∧ VC s' ∧ s'.gpr .r10 = s₂.gpr .r10 := by
  subst hw
  obtain ⟨s, s₁, h, hl, ⟨-, -, -, m₁, rd₁, wr₁, sy₁, g₁⟩, hv⟩ := hi
  have hc0 : ∀ k < 8, candN (fun i => (byteY (s.mem.readW (s.gpr .rsi) 256) i).toNat) (8 * 0 + k) =
      cand4 (xofByte (B σ K)) (3 * (b + t)) k := fun k hk => by
    rw [vcand_eq ht hbt h (by omega), show (8 * 0 + k) / 8 = 0 by omega, show (8 * 0 + k) % 8 = k by omega,
      Nat.mul_zero, Nat.add_zero]
  have hc1 : ∀ k < 8, candN (fun i => (byteY (s.mem.readW (s.gpr .rsi) 256) i).toNat) (8 * 1 + k) =
      cand4 (xofByte (B σ K)) (3 * (b + t) + 12) k := fun k hk => by
    rw [vcand_eq ht hbt h (by omega), show (8 * 1 + k) / 8 = 1 by omega, show (8 * 1 + k) % 8 = k by omega, Nat.mul_one]
  have hA0 := acc4_length (xofByte (B σ K)) (3 * (b + t))
  have hA1 := acc4_length (xofByte (B σ K)) (3 * (b + t) + 12)
  have e0 : cntL (s.mem.readW (s.gpr .rsi) 256) 0 = (acc4 (xofByte (B σ K)) (3 * (b + t))).length := by
    rw [cntL, acc_mask hc0, List.length_map]
  have e1 : cntL (s.mem.readW (s.gpr .rsi) 256) 1 = (acc4 (xofByte (B σ K)) (3 * (b + t) + 12)).length := by
    rw [cntL, acc_mask hc1, List.length_map]
  have hdi : (s₁.gpr .rdi).toNat = (Lt σ K (b + t)).length := by
    rw [g₁ _ (by decide), h.rdi, ofNat64_toNat (by omega)]
  have hbp : s₁.gpr .rbp = poly4W true (aP σ) K := by rw [g₁ _ (by decide), h.rbp]
  refine WP.mono (vputB_ok hv (by rw [g₁ _ (by decide), sy₁]; exact h.lb.tab) (by rw [hdi]; omega)
    (by rw [hbp, hdi, e0]; exact out_reg hp rfl hK h wr₁ (by omega)))
    fun s₂ ⟨hm₂, hdi₂, hsi₂, c₂, rd₂, wr₂, sy₂, g₂⟩ => ?_
  rw [hbp, hdi, e0, m₁] at hm₂
  rw [hdi, e0, e1] at hdi₂
  have hL8 : Lt σ K (b + (t + 8)) = Lt σ K (b + t) ++ acc4 (xofByte (B σ K)) (3 * (b + t)) ++
      acc4 (xofByte (B σ K)) (3 * (b + t) + 12) := by
    have hl' : (sampleAfter [] (xofByte (B σ K)) (b + t)).length < 241 := hl
    rw [← Nat.add_assoc]; exact sampleAfter_eight (by rw [n_eq]; omega)
  have ca : ∀ n, cAddr true (poly4W true (aP σ) K) n = poly4W true (aP σ) K + BitVec.ofNat 64 (2 * n) := fun _ => rfl
  have st0 := stored_write8 h.stored (by omega) hA0 (compW (s.mem.readW (s.gpr .rsi) 256) 0)
    (comp_words (by decide) hc0)
  have st1 := stored_write8 st0 (by rw [List.length_append]; omega) hA1 (compW (s.mem.readW (s.gpr .rsi) 256) 1)
    (comp_words (by decide) hc1)
  rw [ca, ca, List.length_append] at st1
  have hf : Frame [cRegion true (poly4W true (aP σ) K)] s.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by simp only [cw, ↓reduceIte]; omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by simp only [cw, ↓reduceIte]; omega) (by omega))
  have gk : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₂ r h1 h2 h3 h4, g₁ r h1]
  refine ⟨⟨h.lb.poly hp hK hf (rd₂.trans rd₁) (wr₂.trans wr₁) (fun r hr => gk r ?_ ?_ ?_ ?_) (sy₂.trans sy₁), ?_, ?_,
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), h.rbp], by rw [hL8, hm₂]; exact st1⟩, c₂,
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), hv.gpr _ (by decide) (by decide) (by decide),
      g₁ _ (by decide)]⟩
  all_goals try (simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [hsi₂, g₁ _ (by decide), h.rsi, show (24 : BitVec 64) = BitVec.ofNat 64 24 from rfl, Offset.add_add]
    exact congrArg (fun x => at' σ (oBuf + 504 * K) + BitVec.ofNat 64 x) (by omega)
  · rw [hL8]
    apply BitVec.eq_of_toNat_eq
    simp only [List.length_append, BitVec.toNat_ofNat]
    omega

/-- The stores of eight iterations' coefficients, after `vcand`. -/
theorem vec2_ok (hw : w16 = true) {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 8 ≤ 168)
    (hbt : b + t + 8 ≤ 280) {s₁ : State} (hi : VIW w16 σ s₀ K b t s₁) :
    WP isa (.block vput) s₁ fun s' =>
      LAtW w16 σ s₀ K b (t + 8) s' ∧ VC s' ∧ s'.gpr .r10 = s₁.gpr .r10 := by
  rw [show vput = vputA ++ vputB from rfl, WP.block_append_iff]
  exact WP.mono (vec2a_ok hp hw hK hi) fun s₂ ⟨hv, g₂⟩ =>
    WP.mono (vec2b_ok hp hw hK ht hbt hv) fun s' ⟨l', c', h10⟩ => ⟨l', c', by rw [h10, g₂]⟩

/-- Eight iterations with the vector code, from fewer than 241 coefficients. -/
theorem vec_ok (hw : w16 = true) {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 8 ≤ 168)
    (hbt : b + t + 8 ≤ 280) {s : State} (h : LAtW w16 σ s₀ K b t s) (hv : VC s) (hl : (Lt σ K (b + t)).length < 241) :
    WP isa (.seq (.block vcand) (.block vput)) s fun s' =>
      LAtW w16 σ s₀ K b (t + 8) s' ∧ VC s' ∧ s'.gpr .r10 = s.gpr .r10 :=
  WP.seq (WP.mono (vec1_ok hp hK ht h hv hl) fun s₁ ⟨hi, g₁⟩ =>
    WP.mono (vec2_ok hp hw hK ht hbt hi) fun s' ⟨l', c', h10⟩ => ⟨l', c', by rw [h10, g₁]⟩)

omit hp in
theorem cmp241_ok (s : State) :
    WP isa (.block [.alu .cmp .rdi (.imm 241)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .rdi).toNat < 241)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ x l, s'.lane x l = s.lane x l := by
  xrun [show BitVec.signExtend 64 (241 : BitVec 32) = 241 by decide, show (241 : BitVec 64).toNat = 241 from rfl]
  exact fun _ _ => rfl

/-- Eight iterations of the loop. -/
theorem vgrp_ok {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t + 8 ≤ 168) (hbt : b + t + 8 ≤ 280) {s : State}
    (h : LVW w16 σ s₀ K b t s) :
    WP isa (vgrp w16) s fun s' => LVW w16 σ s₀ K b (t + 8) s' ∧ s'.gpr .r10 = s.gpr .r10 := by
  cases w16 with
  | false =>
    exact WP.mono (sca_ok hp hK ht hbt h.lat) fun s' ⟨l', h10⟩ => ⟨⟨l', fun hw => absurd hw (by decide)⟩, h10⟩
  | true =>
    show WP isa (.seq (.block [.alu .cmp .rdi (.imm 241)]) (.ite .b (.seq (.block vcand) (.block vput)) (sca8 true)))
      s _
    refine WP.seq (WP.mono_syms (cmp241_ok s) fun s₁ ⟨hcf, hm, hg, hrd, hwr, hl⟩ sy => ?_)
    have l₁ : LAtW true σ s₀ K b t s₁ := h.lat.same hg hm hrd hwr sy
    have hlen : (Lt σ K (b + t)).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ (b + t)
    rw [h.lat.rdi, ofNat64_toNat (by bdd_omega)] at hcf
    refine WP.ite _ hcf (fun hb => ?_) fun hb => ?_
    · have hb' : (Lt σ K (b + t)).length < 241 := of_decide_eq_true hb
      exact WP.mono (vec_ok hp rfl hK ht hbt l₁ ((h.vc rfl hb').same hl) hb') fun s' ⟨l', c', h10⟩ =>
        ⟨⟨l', fun _ _ => c'⟩, by rw [h10, hg]⟩
    · have hb' : ¬ (Lt σ K (b + t)).length < 241 := of_decide_eq_false hb
      exact WP.mono (sca_ok hp hK ht hbt l₁) fun s' ⟨l', h10⟩ =>
        ⟨⟨l', fun _ h' => absurd (Nat.lt_of_le_of_lt (Lt_mono σ K (b + t) 8) (by rwa [Nat.add_assoc])) hb'⟩,
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
  refine WP.seq (WP.mono (vgrp_ok hp hK (by bdd_omega) (by bdd_omega) hs) fun s₂ ⟨h₂, g₂⟩ =>
      WP.mono_syms (sub10_ok s₂) fun s₃ ⟨⟨hm, h10', hz, hl⟩, k⟩ sy => ?_)
  have e : 8 * i + 8 = 8 * (i + 1) := by bdd_omega
  rw [e] at h₂
  exact ⟨⟨h₂.lat.same' hm k sy, fun hw h' => (h₂.vc hw h').same hl⟩, by rw [h10', g₂], by rw [hz, g₂]⟩

omit hp in
/-- `vzeroupper` changes no register or memory the invariants see. -/
theorem vz_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun s' => s'.mem = s.mem ∧ Keep [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left', Keep]
  exact ⟨rfl, fun _ _ => rfl, rfl, rfl⟩

end

end VG.Proof.MlKem.X86_64.S4
