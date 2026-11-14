module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtRoot
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.TwoStages
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Twos
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.WordLoops
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Divs
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.ShiftStages
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the square root's end

`finishX`: the remainder's zero test into the mask, and the root `D / 2`
shifted right by the normalization's `32 K + z / 2` bits (by words, through
`stageR`, then by bits), less one where `X` was zero; and `sqrt_ok`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (isqrt)

/-! ## The word stages of the root's shift -/

/-- `sB2 := ` the mask of `K & c = 0`. -/
theorem kSel_ok {s : State} {B : Addr} {Z W : Nat} (hw : Ws s B Z W) {K c : Nat} (hK : K < 2 ^ 63) (hc : c < 2 ^ 31)
    (hk : word s.mem B (8 * sK2) = BitVec.ofNat 64 K) :
    WP isa (.block [.mov .rax (.mem (hdr sK2)), .alu .and .rax (.imm (BitVec.ofNat 32 c)),
      .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .store (hdr sB2) .rax]) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sB2)) (mask (decide (K &&& c = 0))) ∧ Keep [.rax] s t := by
  have h256 := hw.h256
  have hn := hw.scr.nowrap
  refine WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sB2)) (mask (decide (K &&& c = 0)))) ?_ rfl
  xrun [State.ea, hdr, hw.rdi, hdrOff, hw.scr.ld (d := 8 * sK2) (by unfold sK2 sFn; omega_arith),
    hw.scr.st (d := 8 * sB2) (by unfold sB2 sFn; omega_arith), hk, sx_ofNat hc, decide_lt_one']
  have e : (BitVec.ofNat 64 K &&& BitVec.ofNat 64 c = 0) ↔ K &&& c = 0 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show K < 2 ^ 64 by omega_using [hK]), Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_using [hc])]
    rfl
  rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (BitVec.ofNat 64 K &&& BitVec.ofNat 64 c = 0)))) =
    mask (decide (BitVec.ofNat 64 K &&& BitVec.ofNat 64 c = 0)) from rfl, decide_eq_decide.mpr e]

/-- What `stageR` changes: the arrays `sqT` and `sqR`, and `sB2`. -/
def rsRs (W : Nat) : List (Nat × Nat) := [(slot W sqT, 8 * (W + 2)), (slot W sqR, 8 * W), (8 * sB2, 8)]

theorem rsR_trans {B : Addr} {W : Nat} {a b c : State} (h₁ : Frm B (rsRs W) a.mem b.mem ∧ Keep mmRegs a b)
    (h₂ : Frm B (rsRs W) b.mem c.mem ∧ Keep mmRegs b c) : Frm B (rsRs W) a.mem c.mem ∧ Keep mmRegs a c :=
  ⟨h₁.1.trans h₂.1, (h₁.2.trans h₂.2).mono (by simp [mmRegs])⟩

/-- A stage's guard: `CF` of `W < c + 4`. -/
theorem stageRHd_ok {s : State} {B : Addr} {Z W : Nat} (hw : Ws s B Z W) {c : Nat} (hc : c ≤ 128) :
    WP isa (.block (ws ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 4)))] : List Instr))) s fun t =>
      (t.cf = some (decide (W < c + 4)) ∧ t.mem = s.mem) ∧ Keep [.r12, .r9] s t := by
  have hw2 := hw.w2
  rw [WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.cf = some (decide (W < c + 4)) ∧ t.mem = s₁.mem) (by
    xrun [h12, sx_ofNat (show c + 4 < 2 ^ 31 by omega_arith)]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt (show c + 4 < 2 ^ 64 by omega_arith)]) rfl)
    fun t ⟨⟨hcf, m₂⟩, k₂⟩ => ⟨⟨hcf, by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by simp)⟩

/-- A stage of `c` words of the root's word shift `K`: where `K & c ≠ 0` (and `c + 4 ≤ W`),
`R := R / 2^(64 c)`. -/
theorem stageR_ok {s : State} {B : Addr} {Z W : Nat} (hw : Ws s B Z W) {V K : Nat} (hK : K < 2 ^ 63)
    (hV : wv s.mem B (slot W sqR) W = V) (hk : word s.mem B (8 * sK2) = BitVec.ofNat 64 K) {c : Nat} (hc : 1 ≤ c)
    (hc64 : c ≤ 64) :
    WP isa (stageR c) s fun t =>
      wv t.mem B (slot W sqR) W = (if c + 4 ≤ W ∧ K &&& c ≠ 0 then V / 2 ^ (64 * c) else V) ∧
      Frm B (rsRs W) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z W := by
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hw2 := hw.w2
  have slR : slot W sqR = 256 + 2 * (8 * (W + 2)) := rfl
  have slT : slot W sqT = 256 + 6 * (8 * (W + 2)) := rfl
  have hsb : 8 * sB2 = 216 := rfl
  have hsk : 8 * sK2 = 248 := rfl
  unfold stageR
  refine WP.seq (WP.mono (stageRHd_ok hw (by omega_arith)) fun s₁ ⟨⟨hcf, m₁⟩, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z W := hw.congrP (P := fun _ => False) (fun _ _ => by rw [m₁]) (fun _ f => f.elim) k₁ (by simp)
  refine WP.ite (decide (W < c + 4)) (by simp only [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · have hg : ¬ (c + 4 ≤ W) := by simp only [decide_eq_true_eq] at hb; omega_arith
    refine WP.block_nil_iff.mpr ⟨?_, ?_, k₁.mono (by simp [mmRegs]), h₁⟩
    · simp only [hg, false_and, ↓reduceIte]; rw [m₁, hV]
    · rw [m₁]; exact Frm.refl _ _ _
  · have hg : c + 4 ≤ W := by simp only [decide_eq_false_iff_not] at hb; omega_arith
    simp only [List.cons_append, List.nil_append]
    refine WP.seq (WP.mono (kSel_ok h₁ hK (by omega_arith) (by rw [m₁, hk])) fun s₂ ⟨m₂, k₂⟩ => ?_)
    have h₂ := h₁.congrW m₂ (by unfold DOk; simp only [sB2, sFn]; omega_arith) (by decide) k₂ (by simp)
    have o₂ : Outside B (8 * sB2) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    have hk₂ := (show word s₂.mem B (8 * sB2) = _ by rw [m₂, word_writeW_self])
    have V₂ : wv s₂.mem B (slot W sqR) W = V := by rw [o₂.wv (by omega_arith) (by omega_arith), m₁, hV]
    show WP isa (seqs (shrWords sqR c sqT ++ [selK false sqR sqT])) s₂ _
    refine wp_seqs_append (by simp [shrWords]) (by simp) (WP.mono (shrWords_ok h₂ (j := sqR) (t := sqT) (by decide)
      (by decide) (by decide) hc (by omega_arith) hc64) fun s₃ ⟨v3, o3, k3⟩ => ?_)
    have h₃ := h₂.congrO o3 (by omega_arith) k3 (by simp)
    simp only [seqs]
    refine WP.mono (selK_ok h₃ false (j := sqR) (t := sqT) (keep := decide (K &&& c = 0)) (by simp; decide)
      (by simp; decide) (by simp only [shlN, Bool.false_eq_true, ↓reduceIte]; omega_arith)
      (by rw [o3.word (by omega_arith) (by omega_arith), hk₂])) fun t ⟨v4, o4, k4⟩ => ?_
    simp only [shlN, Bool.false_eq_true, ↓reduceIte] at v4 o4
    have T₃ : wv s₃.mem B (slot W sqT) W = V / 2 ^ (64 * c) := by
      rw [← wv_mod_low s₃.mem B _ (show W ≤ W + 2 by omega_arith), v3, V₂,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by rw [← V₂]; exact wv_lt _ _ _ _))]
    refine ⟨?_, ?_, (((k₁.trans k₂).trans k3).trans k4).mono (by simp [mmRegs]),
      h₃.congrO o4 (by omega_arith) k4 (by simp)⟩
    · rw [v4, o3.wv (by omega_arith) (by omega_arith), V₂, T₃]
      by_cases hq : K &&& c = 0 <;> simp [hq, hg]
    · rw [← m₁]
      exact ((Frm.of_outside o₂ (by simp [rsRs])).trans (Frm.of_outside o3 (by simp [rsRs]))).trans
        (Frm.of_outside o4 (by simp [rsRs]))

/-- The word stages of the root's shift `K`, in turn. -/
def rnF (W K V : Nat) : List Nat → Nat
  | [] => V
  | c :: cs => rnF W K (if c + 4 ≤ W ∧ K &&& c ≠ 0 then V / 2 ^ (64 * c) else V) cs

theorem rnStages_ok {B : Addr} {Z W K : Nat} (hK : K < 2 ^ 63) : ∀ (cs : List Nat), (∀ c ∈ cs, 1 ≤ c ∧ c ≤ 64) →
    cs ≠ [] → ∀ {s : State} {V : Nat}, Ws s B Z W → wv s.mem B (slot W sqR) W = V →
    word s.mem B (8 * sK2) = BitVec.ofNat 64 K →
    WP isa (seqs (cs.map stageR)) s fun t =>
      wv t.mem B (slot W sqR) W = rnF W K V cs ∧ Frm B (rsRs W) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z W
  | [], _, h0, _, _, _, _, _ => absurd rfl h0
  | [c], hc, _, s, V, hw, hV, hk => by
    have hc' := hc c (by simp)
    simp only [List.map_cons, List.map_nil, seqs]
    exact WP.mono (stageR_ok hw hK hV hk hc'.1 hc'.2) fun t ⟨v, f, k, ht⟩ => ⟨by rw [v]; rfl, f, k, ht⟩
  | c :: c' :: cs, hc, _, s, V, hw, hV, hk => by
    have hc' := hc c (by simp)
    have hn := hw.scr.nowrap
    have h256 := hw.h256
    have hZ := hw.hZ
    rw [slotE] at hZ
    rw [List.map_cons, show seqs (stageR c :: (c' :: cs).map stageR) = .seq (stageR c) (seqs ((c' :: cs).map stageR))
      from rfl]
    refine WP.seq (WP.mono (stageR_ok hw hK hV hk hc'.1 hc'.2) fun t ⟨v, f, k, ht⟩ => ?_)
    have hk' : word t.mem B (8 * sK2) = BitVec.ofNat 64 K := by
      rw [f.word_eq (fun r hr => by
        simp only [rsRs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [Bignum.slot, hdrBytes, sqT, sqR, sK2, sB2, sFn] <;> omega_arith)
        (by simp only [sK2, sFn]; omega_arith), hk]
    exact WP.mono (rnStages_ok hK (c' :: cs) (fun x hx => hc x (by simp [hx])) (by simp) ht v hk')
      fun u ⟨u1, f', k', hu⟩ => ⟨u1, (rsR_trans ⟨f, k⟩ ⟨f', k'⟩).1, (rsR_trans ⟨f, k⟩ ⟨f', k'⟩).2, hu⟩

theorem and_pow_ne {K i : Nat} : K &&& 2 ^ i ≠ 0 ↔ K / 2 ^ i % 2 = 1 := by
  have key : (K &&& 2 ^ i).testBit i = decide (K / 2 ^ i % 2 = 1) := by
    rw [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, Nat.testBit_eq_decide_div_mod_eq]
  have other : ∀ j, j ≠ i → (K &&& 2 ^ i).testBit j = false := fun j hj => by
    rw [Nat.testBit_and, Nat.testBit_two_pow_of_ne (Ne.symm hj), Bool.and_false]
  constructor
  · intro h
    by_contra h'
    apply h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.zero_testBit]
    by_cases hj : j = i
    · subst hj; rw [key]; simp [h']
    · exact other j hj
  · intro h h0
    rw [h0, Nat.zero_testBit] at key
    simp [h] at key

open VG.Proof.Bignum.ShiftStages in
/-- The stages `pows k` shift `V` right by `K`'s low `k + 1` bits' words, for `K + 4 ≤ W`. -/
theorem rnF_val {W K : Nat} (hKW : K + 4 ≤ W) : ∀ (k V : Nat), rnF W K V (pows k) = V / 2 ^ (64 * (K % 2 ^ (k + 1)))
  | 0, V => by
    simp only [pows, rnF, Nat.and_one_is_mod, Nat.zero_add, Nat.pow_one]
    rcases Nat.mod_two_eq_zero_or_one K with h | h
    · simp [h]
    · simp only [h, show 1 + 4 ≤ W by omega_using [hKW, h], ne_eq, Nat.one_ne_zero, not_false_eq_true, and_self, ↓reduceIte,
        Nat.mul_one]
  | k + 1, V => by
    rw [pows, rnF, rnF_val hKW k, Nat.mod_pow_succ (k := k + 1)]
    by_cases hb : K / 2 ^ (k + 1) % 2 = 1
    · have hc : 2 ^ (k + 1) + 4 ≤ W := by
        have h1 : 1 * 2 ^ (k + 1) ≤ K :=
          (Nat.le_div_iff_mul_le (Nat.two_pow_pos (k + 1))).mp
            (Nat.pos_of_ne_zero fun h => by rw [h] at hb; simp at hb)
        rw [Nat.one_mul] at h1
        generalize 2 ^ (k + 1) = P at h1 ⊢
        omega_using [hKW, h1]
      simp only [hc, and_pow_ne.mpr hb, ne_eq, not_false_eq_true, and_self, ↓reduceIte, hb, Nat.mul_one,
        Nat.div_div_eq_div_mul, ← Nat.pow_add]
      congr 2; omega_using []
    · have hb0 : K / 2 ^ (k + 1) % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one (K / 2 ^ (k + 1)) with h | h
        · exact h
        · exact absurd h hb
      have : ¬ (K &&& 2 ^ (k + 1) ≠ 0) := fun h => hb (and_pow_ne.mp h)
      simp only [this, and_false, ↓reduceIte, hb0, Nat.mul_zero, Nat.add_zero]

/-! ## The bit shift and the end -/

/-- `K := K / 2` and `sC := z / 2 + 32 (K mod 2)`. -/
theorem kBlk_ok {s : State} {B : Addr} {Z W : Nat} (hw : Ws s B Z W) {K z : Nat} (hK : K < 2 ^ 63) (hz : z < 64)
    (hk : word s.mem B (8 * sK2) = BitVec.ofNat 64 K) (hc : word s.mem B (8 * sC) = BitVec.ofNat 64 z) :
    WP isa (.block [.mov .rax (.mem (hdr sK2)), .mov .rdx (.reg .rax), .shift .shr .rax 1, .store (hdr sK2) .rax,
      .alu .and .rdx (.imm 1), .shift .shl .rdx 5, .mov .rax (.mem (hdr sC)), .shift .shr .rax 1,
      .alu .add .rax (.reg .rdx), .store (hdr sC) .rax]) s fun t =>
      t.mem = (s.mem.writeW (off B (8 * sK2)) (BitVec.ofNat 64 (K / 2))).writeW (off B (8 * sC))
        (BitVec.ofNat 64 (z / 2 + 32 * (K % 2))) ∧ Keep [.rax, .rdx] s t := by
  have h256 := hw.h256
  have hn := hw.scr.nowrap
  refine WP.keep [.rax, .rdx] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * sK2)) (BitVec.ofNat 64 (K / 2))).writeW
    (off B (8 * sC)) (BitVec.ofNat 64 (z / 2 + 32 * (K % 2)))) ?_ rfl
  have shv1 : (1 ≤ 1 ∧ 1 ≤ 63) = True := eq_true ⟨by decide, by decide⟩
  have shv5 : (1 ≤ 5 ∧ 5 ≤ 63) = True := eq_true ⟨by decide, by decide⟩
  have e1 : BitVec.ofNat 64 K >>> 1 = BitVec.ofNat 64 (K / 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using [hK]
  have e2 : BitVec.ofNat 64 z >>> 1 + (BitVec.ofNat 64 K &&& 1) <<< 5 =
      BitVec.ofNat 64 (z / 2 + 32 * (K % 2)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.and_one_is_mod, Nat.mod_eq_of_lt (show K < 2 ^ 64 by omega_using [hK]),
      Nat.mod_eq_of_lt (show z < 2 ^ 64 by omega_using [hz])]
    omega_using []
  xrun [State.ea, hdr, hw.rdi, hdrOff, hw.scr.ld (d := 8 * sK2) (by unfold sK2 sFn; omega_arith),
    hw.scr.st (d := 8 * sK2) (by unfold sK2 sFn; omega_arith), hk, shv1, shv5, e1,
    hw.scr.ld (d := 8 * sC) (by unfold sC sFn; omega_arith), hw.scr.st (d := 8 * sC) (by unfold sC sFn; omega_arith), hc,
    word_wW (d := 8 * sK2) (d' := 8 * sC) _ (by unfold sK2 sC sFn; omega_arith) (by unfold sK2 sFn; omega_arith)
      (by unfold sC sFn; omega_arith)]
  rw [e2]

/-- The last block: the root's word 0 less `1` where `X` was zero (`sZ`). -/
theorem lastR_ok {s : State} {B : Addr} {Z W : Nat} (hw : Ws s B Z W) {b : Bool}
    (hz : word s.mem B (8 * sZ) = mask b) :
    WP isa (.block (ws ++ base sqR .rbx ++ ([.mov .rax (.mem (hdr sZ)), .alu .and .rax (.imm 1),
      .mov .rdx (.mem (at0 .rbx)), .alu .sub .rdx (.reg .rax), .store (at0 .rbx) .rdx] : List Instr))) s fun t =>
      t.mem = s.mem.writeW (off B (slot W sqR)) (word s.mem B (slot W sqR) - (if b then 1 else 0)) ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx] s t := by
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  rw [slotE] at hZ
  have slR : slot W sqR = 256 + 2 * (8 * (W + 2)) := rfl
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok sqR (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hw.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hw.scr.congr k12.2.2
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s.mem.writeW (off B (slot W sqR))
      (word s.mem B (slot W sqR) - (if b then 1 else 0))) (by
    have hdi : s₂.gpr .rdi = B := (k12.gpr (by decide)).trans hw.rdi
    have a0 : s₂.gpr .rbx + BitVec.ofInt 64 0 = off B (slot W sqR) := by
      rw [hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    have e : mask b &&& 1 = if b then 1 else 0 := by cases b <;> decide
    xrun [State.ea, hdr, at0, hdi, hdrOff, a0, hs₂.ld (d := 8 * sZ) (by unfold sZ sFn; omega_arith),
      hs₂.ld (d := slot W sqR) (by omega_arith), hs₂.st (d := slot W sqR) (by omega_arith), m₂, m₁, hz]
    rw [e]) rfl)
    fun t ⟨m₃, k₃⟩ => ⟨m₃, (k12.trans k₃).mono (by simp)⟩

/-- What `finishX` changes: the mask, `sB2`, `sC`, `sK2`, and the arrays `sqR` and `sqT`. -/
def FinP (W y : Nat) : Prop :=
  (176 ≤ y ∧ y < 184) ∨ (216 ≤ y ∧ y < 224) ∨ (240 ≤ y ∧ y < 256) ∨
    (slot W sqR ≤ y ∧ y < slot W sqR + 8 * (W + 2)) ∨ (slot W sqT ≤ y ∧ y < slot W sqT + 8 * (W + 2))

/-- `finishX`, after the loop (count 0) on `X'`: the root of `X'` shifted right by
`32 C + z / 2` bits, less `1` where `sZ` is set, and the mask and'ed with
whether the remainder is zero. -/
theorem finishX_ok {t₀ t : State} {B : Addr} {Z W h X C z : Nat} {c b : Bool} (hwh : W = 2 * h + 4) (h1 : 1 ≤ h)
    (hh : h ≤ 128) (hI : SqI t₀ B Z W h X 0 t) (hk : word t.mem B (8 * sK2) = BitVec.ofNat 64 C) (hC : C + 1 ≤ 2 * h)
    (hzc : word t.mem B (8 * sC) = BitVec.ofNat 64 z) (hz64 : z < 64) (hsz : word t.mem B (8 * sZ) = mask b)
    (hm : mw t.mem B = mask c) (hb : b = true → isqrt X / 2 ^ (32 * C + z / 2) = 1) :
    WP isa (seqs finishX) t fun u =>
      wv u.mem B (slot W sqR) W = isqrt X / 2 ^ (32 * C + z / 2) - (if b then 1 else 0) ∧
      mw u.mem B = mask (c && decide (X - isqrt X * isqrt X = 0)) ∧ FrmP B (FinP W) t.mem u.mem ∧
      Keep mmRegs t u ∧ Ws u B Z W := by
  have hw := hI.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hw2 := hw.w2
  have slR : slot W sqR = 256 + 2 * (8 * (W + 2)) := rfl
  have slT : slot W sqT = 256 + 6 * (8 * (W + 2)) := rfl
  have slZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have slD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have hsb : 8 * sB2 = 216 := rfl
  have hsk : 8 * sK2 = 248 := rfl
  have hsc : 8 * sC = 240 := rfl
  have hsz' : 8 * sZ = 232 := rfl
  have hsm : 8 * Impl.Bignum.X86_64.Public.sMask = 176 := rfl
  have hz := hI.z
  have hd := hI.d
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_add, Nat.mul_one, Ap, Nat.div_one] at hz hd
  generalize hs : isqrt X = s at hz hd hb ⊢
  unfold finishX
  -- The remainder's zero test.
  refine WP.seq (WP.seq (WP.mono (orXHd_ok hw) fun s₁ ⟨hbx, hbp, h12, m₁, k₁⟩ => ?_))
  refine WP.mono (or1_ok (hw.scr.congr k₁.2.2) hbx h12 (by omega_arith) (by omega_arith) (by omega_arith))
    fun t₁ ⟨hz₁, m₁', k₁'⟩ => ?_
  have mm₁ : t₁.mem = t.mem := by rw [m₁', m₁]
  have hz' : t₁.gpr .rbp = 0 ↔ X - s * s = 0 := by rw [hz₁, hbp, m₁, hz]; simp
  have h₁ : Ws t₁ B Z W :=
    hw.congrP (P := fun _ => False) (fun _ _ => by rw [mm₁]) (fun _ f => f.elim) (k₁.trans k₁') (by simp)
  -- The mask.
  refine WP.seq (WP.mono (andZero_ok h₁ (c := c) (by rw [mm₁]; exact hm) hz') fun t₂ ⟨m₂, k₂⟩ => ?_)
  rw [mm₁] at m₂
  have h₂ := hw.congrW m₂ (by unfold DOk; decide) (by decide) ((k₁.trans k₁').trans k₂) (by simp)
  have o₂ : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t.mem t₂.mem := by
    rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
  -- `R := D / 2`.
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := sqR) (by decide)) fun t₃ ⟨z3, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by omega_arith) k3 (by simp)
  refine WP.seq (WP.mono (shrTo_ok h₃ (j := sqD) (o := sqR) (by decide) (by decide) (by decide)
    (by rw [o3.word (by omega_arith) (by omega_arith), o₂.word (by omega_arith) (by omega_arith)]; exact hI.dtop))
    fun t₄ ⟨v4, o4, k4⟩ => ?_)
  have h₄ := h₃.congrO o4 (by omega_arith) k4 (by simp)
  rw [o3.wv (by omega_arith) (by omega_arith), o₂.wv (by omega_arith) (by omega_arith), hd,
    show 2 * s / 2 = s by omega_using []] at v4
  have Rtop₄ : word t₄.mem B (slot W sqR + 8 * W) = 0 := by
    rw [o4.word (by omega_arith) (by omega_arith)]; exact (wv_eq_zero_iff _ _ _ _).mp z3 W (by omega_arith)
  -- `K := K / 2`, `sC := z / 2 + 32 (K mod 2)`.
  have back : ∀ d, d + 8 ≤ 256 → (d + 8 ≤ 176 ∨ 184 ≤ d) → word t₄.mem B d = word t.mem B d := fun d h1 h2 => by
    rw [o4.word (by omega_arith) (by omega_arith), o3.word (by omega_arith) (by omega_arith),
      o₂.word (by omega_arith) (by omega_arith)]
  refine WP.seq (WP.mono (kBlk_ok h₄ (K := C) (z := z) (by omega_arith) hz64 (by rw [back _ (by omega_arith)
    (by omega_arith), hk]) (by rw [back _ (by omega_arith) (by omega_arith), hzc])) fun t₅ ⟨m5, k5⟩ => ?_)
  have FP₅ : FrmP B (fun y => 240 ≤ y ∧ y < 256) t₄.mem t₅.mem := by
    intro x hx
    rw [m5, writeW_outside _ B _ (d := 8 * sC) (by omega_arith) x (by omega),
      writeW_outside _ B _ (d := 8 * sK2) (by omega_arith) x (by omega)]
  have h₅ := h₄.congrP FP₅ (fun y hy => by unfold DOk; omega_arith) k5 (by decide)
  have K₅ : word t₅.mem B (8 * sK2) = BitVec.ofNat 64 (C / 2) := by
    rw [m5, word_wW (d := 8 * sC) _ (by omega_arith) (by omega_arith) (by omega_arith), word_writeW_self]
  have C₅ : word t₅.mem B (8 * sC) = BitVec.ofNat 64 (z / 2 + 32 * (C % 2)) := by rw [m5, word_writeW_self]
  have R₅ : wv t₅.mem B (slot W sqR) W = s := by rw [FP₅.wv_eq (fun y h1 h2 hy => by omega_arith) (by omega_arith), v4]
  -- The word stages.
  refine wp_seqs_append (by simp [wordStages]) (by simp) (WP.mono (rnStages_ok (W := W) (K := C / 2) (by omega_arith)
    wordStages (by decide) (by simp [wordStages]) h₅ R₅ K₅) fun t₆ ⟨v6, f6, k6, h₆⟩ => ?_)
  rw [pows6, rnF_val (by omega_arith) 6, Nat.mod_eq_of_lt (show C / 2 < 2 ^ (6 + 1) by omega_arith)] at v6
  have fr6 : ∀ d, (d + 8 ≤ slot W sqT ∨ slot W sqT + 8 * (W + 2) ≤ d) → (d + 8 ≤ slot W sqR ∨ slot W sqR + 8 * W ≤ d) →
      (d + 8 ≤ 216 ∨ 224 ≤ d) → d + 8 ≤ 2 ^ 64 → word t₆.mem B d = word t₅.mem B d := fun d a1 a2 a3 a4 =>
    f6.word_eq (fun r hr => by
      simp only [rsRs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) a4
  -- The bit shift, and the copy back.
  simp only [seqs]
  refine WP.seq (WP.mono (shrClP_ok h₆ (j := sqR) (t := sqT) (by decide) (by decide) (by decide)
    (show z / 2 + 32 * (C % 2) < 64 by omega_arith) (sC_pre (by omega_arith) (by
      rw [fr6 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), C₅]))
    (by rw [fr6 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      FP₅.word_eq (fun y h1 h2 hy => by omega_arith) (by omega_arith), Rtop₄])) fun t₇ ⟨v7, o7, k7⟩ => ?_)
  have h₇ := h₆.congrO o7 (by omega_arith) k7 (by simp)
  refine WP.seq (WP.mono (copyA_ok h₇ (o := sqR) (a := sqT) (by decide) (by decide) (by decide))
    fun t₈ ⟨v8, o8, k8⟩ => ?_)
  have h₈ := h₇.congrO o8 (by omega_arith) k8 (by simp)
  rw [v7, v6, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 64 * (C / 2) + (z / 2 + 32 * (C % 2)) = 32 * C + z / 2 by omega_arith] at v8
  -- The last block.
  have Z₈ : word t₈.mem B (8 * sZ) = mask b := by
    rw [o8.word (by omega_arith) (by omega_arith), o7.word (by omega_arith) (by omega_arith),
      fr6 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      FP₅.word_eq (fun y h1 h2 hy => by omega_arith) (by omega_arith), back _ (by omega_arith) (by omega_arith), hsz]
  refine WP.mono (lastR_ok h₈ Z₈) fun u ⟨m9, k9⟩ => ?_
  have o9 : Outside B (slot W sqR) 8 t₈.mem u.mem := by rw [m9]; exact writeW_outside _ _ _ (by omega_arith)
  have kall : Keep mmRegs t u :=
    (((((((((k₁.trans k₁').trans k₂).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9).mono
      (by simp [mmRegs])
  refine ⟨?_, ?_, ?_, kall, h₈.congrO o9 (by omega_arith) k9 (by simp)⟩
  · have sp := wv_add t₈.mem B (slot W sqR) 1 (W - 1)
    have sp' := wv_add u.mem B (slot W sqR) 1 (W - 1)
    rw [show 1 + (W - 1) = W by omega_arith, wv_one', show 64 * 1 = 64 from rfl,
      show slot W sqR + 8 * 1 = slot W sqR + 8 from rfl] at sp sp'
    rw [sp', o9.wv (by omega_arith) (by omega_arith), m9, word_writeW_self]
    rw [v8] at sp
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
      rw [show ∀ x : BitVec 64, x - 0 = x from fun x => by simp]
      exact sp.symm
    · have h1v := hb rfl
      rw [h1v] at sp ⊢
      have hw0 : (word t₈.mem B (slot W sqR)).toNat = 1 := by
        rcases Nat.eq_zero_or_pos (wv t₈.mem B (slot W sqR + 8) (W - 1)) with e | e
        · omega_arith
        · have : 2 ^ 64 ≤ 2 ^ 64 * wv t₈.mem B (slot W sqR + 8) (W - 1) := Nat.le_mul_of_pos_right _ e
          omega_arith
      have hr0 : wv t₈.mem B (slot W sqR + 8) (W - 1) = 0 := by omega_arith
      simp only [↓reduceIte, hr0, Nat.mul_zero, Nat.add_zero]
      rw [BitVec.toNat_sub, hw0, show (1 : BitVec 64).toNat = 1 from rfl]
  · unfold mw
    rw [o9.word (by omega_arith) (by omega_arith), o8.word (by omega_arith) (by omega_arith),
      o7.word (by omega_arith) (by omega_arith), fr6 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      FP₅.word_eq (fun y h1 h2 hy => by omega_arith) (by omega_arith), o4.word (by omega_arith) (by omega_arith),
      o3.word (by omega_arith) (by omega_arith), m₂, word_writeW_self]
  · have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → FinP W y) →
        FrmP B (FinP W) m m' := fun ho hP => FrmP.of_out ho hP
    refine ((((((((fr o₂ fun y h1 h2 => by unfold FinP; omega_arith).trans
      (fr o3 fun y h1 h2 => by unfold FinP; omega_arith)).trans (fr o4 fun y h1 h2 => by unfold FinP; omega_arith)).trans
      (FP₅.mono fun y hy => by unfold FinP; omega_arith)).trans (FrmP.of_frm f6 fun r hr y h1 h2 => by
        simp only [rsRs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only at h1 h2 <;> unfold FinP <;> omega_arith)).trans
      (fr o7 fun y h1 h2 => by unfold FinP; omega_arith)).trans (fr o8 fun y h1 h2 => by unfold FinP; omega_arith)).trans
      (fr o9 fun y h1 h2 => by unfold FinP; omega_arith))

/-! ## The square root -/

/-- What the square root changes. -/
def SqrtP (W y : Nat) : Prop := NxP W y ∨ SqLP W y ∨ FinP W y

theorem isqrt_zero : isqrt 0 = 0 := VG.Proof.Rsa.RecoverDet.isqrt_eq (by decide) (by decide)
theorem isqrt_one : isqrt 1 = 1 := VG.Proof.Rsa.RecoverDet.isqrt_eq (by decide) (by decide)

/-- The square root (wide, `W = 2 h + 4`): `[sqR] := ⌊√X₀⌋` for `X₀` the low `2 h`
words of `[sqZ]`, and the mask and'ed with whether `X₀` is a square. -/
theorem sqrt_ok {s : State} {B : Addr} {Z W h X : Nat} {c : Bool} (hw : Ws s B Z W) (hwh : W = 2 * h + 4)
    (h2 : 2 ≤ h) (hh : h ≤ 128) (hX : wv s.mem B (slot W sqZ) W = X) (hm : mw s.mem B = mask c) :
    WP isa (seqs RecoverDet.sqrt) s fun t =>
      wv t.mem B (slot W sqR) W = isqrt (X % 2 ^ (64 * (2 * h))) ∧
      mw t.mem B = mask (c && decide (isqrt (X % 2 ^ (64 * (2 * h))) * isqrt (X % 2 ^ (64 * (2 * h))) =
        X % 2 ^ (64 * (2 * h)))) ∧
      FrmP B (SqrtP W) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z W := by
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hsk : 8 * sK2 = 248 := rfl
  have hsc : 8 * sC = 240 := rfl
  have hsz : 8 * sZ = 232 := rfl
  have hsm : 8 * Impl.Bignum.X86_64.Public.sMask = 176 := rfl
  have slZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have slD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have slS : slot W sqS = 256 + 1 * (8 * (W + 2)) := rfl
  have slU : slot W sqU = 256 + 5 * (8 * (W + 2)) := rfl
  have slT : slot W sqT = 256 + 6 * (8 * (W + 2)) := rfl
  unfold RecoverDet.sqrt
  rw [show normX ++ firstX ++ ([.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr)),
      .loop stepX .ne] : List (Prog isa)) ++ finishX =
    normX ++ ((firstX ++ [.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr))]) ++
      ([.loop stepX .ne] ++ finishX)) by simp]
  refine wp_seqs_append (by simp [normX]) (by simp [firstX]) (WP.mono (normX_ok hw hwh (by omega_using [h2]) hh hX)
    fun t₁ ⟨C, z, hz2, hz64, hC, X₁, hlo, hhi, K₁, Z₁, S₁, F₁, k₁, h₁⟩ => ?_)
  refine wp_seqs_append (by simp [firstX]) (by simp) (WP.mono (sqInit_ok h₁ hwh h2 X₁ hlo hhi)
    fun t₂ ⟨I₂, F₂, k₂⟩ => ?_)
  refine wp_seqs_append (by simp) (by unfold finishX; simp) (WP.mono (sqLoop_ok hwh hh hhi hlo h2 I₂)
    fun t₃ I₃ => ?_)
  -- The header's words, through `firstX` and the loop.
  have keepH : ∀ d, d + 8 ≤ 256 → (d + 8 ≤ 200 ∨ 216 ≤ d) → word t₃.mem B d = word t₁.mem B d := fun d a1 a2 => by
    rw [I₃.frm.word_eq (fun y h1 h2 hy => by unfold SqLP at hy; simp only [sCt, sU, sFn] at hy; omega_arith) (by omega_using [a1]),
      F₂.word_eq (fun y h1 h2 hy => by unfold SqLP at hy; simp only [sCt, sU, sFn] at hy; omega_arith) (by omega_using [a1])]
  -- The normalized number's root.
  generalize hX0 : X % 2 ^ (64 * (2 * h)) = X0 at S₁ ⊢
  have hXn : Xn X h = if X0 = 0 then 1 else X0 := by unfold Xn; rw [hX0]
  have e4 : Xn X h * 2 ^ (64 * C) * 2 ^ z = 4 ^ (32 * C + z / 2) * Xn X h := by
    rw [VG.Proof.Bignum.SqrtRem.four_pow, ← Nat.pow_add, Nat.mul_assoc, ← Nat.pow_add, Nat.mul_comm]
    congr 2; omega_using [hz2]
  have nsq := VG.Proof.Bignum.SqrtRem.norm_sqrt (32 * C + z / 2) (Xn X h)
  have nsq2 := VG.Proof.Bignum.SqrtRem.norm_square (32 * C + z / 2) (Xn X h)
  rw [← e4] at nsq nsq2
  refine WP.mono (finishX_ok (c := c) (b := decide (X0 = 0)) hwh (by omega_using [h2]) hh I₃ (by rw [keepH _ (by omega_using [hsk]) (by omega_using [hsk]), K₁])
    hC (by rw [keepH _ (by omega_using [hsc]) (by omega_using [hsc]), Z₁]) hz64 (by rw [keepH _ (by omega_using [hsz]) (by omega_using [hsz]), S₁])
    (by unfold mw; rw [keepH _ (by omega_using [hsm]) (by omega_using [hsm]), F₁.word_eq (fun y h1 h2 hy => by unfold NxP at hy; omega_arith)
      (by omega_using [hsm])]; exact hm)
    (fun hb => by rw [nsq, hXn]; simp only [of_decide_eq_true hb, ↓reduceIte, isqrt_one])) fun t ⟨R, M, F₄, k₄, h₄⟩ => ?_
  refine ⟨?_, ?_, ?_, (((k₁.trans k₂).trans I₃.keep).trans k₄).mono (by simp [mmRegs]), h₄⟩
  · rw [R, nsq, hXn]
    by_cases h0 : X0 = 0
    · simp only [h0, ↓reduceIte, decide_true, isqrt_one, isqrt_zero]
    · simp only [h0, ↓reduceIte, decide_false, Bool.false_eq_true, Nat.sub_zero]
  · rw [M]
    congr 2
    apply decide_eq_decide.mpr
    rw [show Xn X h * 2 ^ (64 * C) * 2 ^ z - isqrt (Xn X h * 2 ^ (64 * C) * 2 ^ z) *
        isqrt (Xn X h * 2 ^ (64 * C) * 2 ^ z) = 0 ↔
      isqrt (Xn X h * 2 ^ (64 * C) * 2 ^ z) * isqrt (Xn X h * 2 ^ (64 * C) * 2 ^ z) = Xn X h * 2 ^ (64 * C) * 2 ^ z by
      have := VG.Proof.Rsa.RecoverDet.isqrt_sq_le (Xn X h * 2 ^ (64 * C) * 2 ^ z); omega_using [this], nsq2, hXn]
    by_cases h0 : X0 = 0
    · simp only [h0, ↓reduceIte, isqrt_one, isqrt_zero]
    · simp only [h0, ↓reduceIte]
  · exact (((F₁.mono fun y hy => .inl hy).trans (F₂.mono fun y hy => .inr (.inl hy))).trans
      (I₃.frm.mono fun y hy => .inr (.inl hy))).trans (F₄.mono fun y hy => .inr (.inr hy))

end VG.Proof.Rsa.X86_64.Rd
