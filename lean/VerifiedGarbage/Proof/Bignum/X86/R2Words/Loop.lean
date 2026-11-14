module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power

-- separate module: the word steps' proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-!
# `R2Words` on x86: the steps

`count` stores the steps' count `S = ⌊5 B / 16⌋ + 1 - W'` at 176
(`count_ok`), and `steps` runs `S` steps from `x = 2^(32 (W' - 1))`, which
leaves `2^(32 (W' - 1 + S)) mod M` (`steps_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.PublicRt VG.Impl.Bignum.X86.R2Words VG.Proof.Bignum.X86.PrecomputeRt

/-- The steps' count. -/
abbrev nSteps (len : Nat) : Nat := 5 * wb len / 16 + 1 - wp len

/-- `count`: `S` at 176. -/
theorem count_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) :
    WP isa (.block count) s fun t => t.mem = s.mem.writeW (off base oSteps) (BitVec.ofNat 32 (nSteps len)) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have hwp := wp_le_nw (len := len)
  have hb := wb_le h.upper
  have hl := h.lower
  have f0 := (h.fits (j := 0) (by decide)).1
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  simp only [count, List.append_assoc, List.cons_append, List.nil_append]
  refine widthB_ok h.width h.upper fun u₁ K₁ m₁ e₁ => ?_
  refine wp_movS rfl fun u₂ U₂ _ => wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ _ => ?_
  refine wp_shr (by decide) fun u₆ U₆ => wp_addS rfl fun u₇ U₇ _ => ?_
  have K₇ : Keeps [.eax, .ecx] s u₇ := (K₁.mono (by decide)).trans ((((U₂.keeps.mono (by decide)).trans
    (U₃.keeps.mono (by decide))).trans ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide)))).trans
    ((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide))))
  have m₇ : u₇.mem = s.mem := by rw [U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]
  refine width4_ok ((h.stack 1 (by decide)).keep K₇ (by decide) (by rw [m₇]; exact Outside.refl _ _ _ _)
    |>.readSrc |>.trans (by rw [h.wLen])) h.upper fun u₈ K₈ m₈ e₈ => ?_
  refine wp_shr (by decide) fun u₉ U₉ => wp_subS rfl fun u₁₀ U₁₀ _ => ?_
  have K₁₀ : Keeps [.eax, .ecx, .edx] s u₁₀ := (K₇.mono (by decide)).trans ((K₈.mono (by decide)).trans
    ((U₉.keeps.mono (by decide)).trans (U₁₀.keeps.mono (by decide))))
  have ws : Ws u₁₀ base bytes := h.ws.of_wr K₁₀.2.2
  have di : PtrAt u₁₀ base .edi 0 := by
    rw [PtrAt, K₁₀.1 _ (by decide), Nat.add_zero, Nat.mod_eq_of_lt (by omega_using [nw, f0, e0])]; exact h.edi
  refine wp_storeS (ea_ptr ws di (d := oSteps) (by simp only [oSteps]; omega_using [f0, e0]))
    (ws_write ws (by simp only [oSteps]; omega_using [f0, e0])) fun t M => WP.block_nil ⟨?_, K₁₀.trans (M.keeps _)⟩
  rw [M.mem, U₁₀.mem, U₉.mem, m₈, m₇, Nat.zero_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hb32 : wb len < 2 ^ 30 := by omega_using [hb]
  have c₂ : (u₂.gpr .ecx).toNat = wb len := by rw [U₂.gpr, e₁, BitVec.toNat_ofNat]; omega_using [hb]
  have a₂ : (u₂.gpr .eax).toNat = wb len := by rw [U₂.other _ (by decide), e₁, BitVec.toNat_ofNat]; omega_using [hb]
  have a₃ : (u₃.gpr .eax).toNat = 2 * wb len := by rw [U₃.gpr, BitVec.toNat_add, a₂, c₂]; omega_using [hb]
  have a₄ : (u₄.gpr .eax).toNat = 4 * wb len := by rw [U₄.gpr, BitVec.toNat_add, a₃]; omega_using [hb]
  have a₅ : (u₅.gpr .eax).toNat = 5 * wb len := by
    rw [U₅.gpr, BitVec.toNat_add, a₄, U₄.other .ecx (by decide), U₃.other .ecx (by decide), c₂]; omega_using [hb]
  have a₆ : (u₆.gpr .eax).toNat = 5 * wb len / 16 := by
    rw [U₆.gpr, BitVec.toNat_ushiftRight, a₅, Nat.shiftRight_eq_div_pow]
  have a₇ : (u₇.gpr .eax).toNat = 5 * wb len / 16 + 1 := by
    rw [U₇.gpr, BitVec.toNat_add, a₆, show (1 : BitVec 32).toNat = 1 from rfl]; omega_using [hb]
  have hw4 : 4 * wp len < 2 ^ 32 := by omega_using [hwp, hb]
  have d₉ : (u₉.gpr .edx).toNat = wp len := by
    rw [U₉.gpr, BitVec.toNat_ushiftRight, e₈, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hw4]
    omega_using []
  have hle : wp len ≤ 5 * wb len / 16 + 1 := by simp only [wp, wb, Spec.Rsa.modulusWords] at *; omega_using []
  rw [U₁₀.gpr, BitVec.toNat_sub, U₉.other .eax (by decide), K₈.1 .eax (by decide), a₇, d₉, BitVec.toNat_ofNat]
  simp only [nSteps]
  omega_using [hwp, hb, f0, hb32, c₂, a₂, a₃, a₄, a₅, a₆, a₇, hw4, d₉, hle]

/-- What the steps keep, after `i` of them from `s`, with `x = 2^(32 (W' - 1 + i)) mod M`. -/
structure StI (s : State) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (m i : Nat) (u : State) : Prop where
  pi : PcIn base bytes len args u
  keep : Keeps k6 s u
  out : Outside base oMask (numAt len 5 + 4 * (wp len + 1) - oMask) s.mem u.mem
  mid : ∀ o, oU2 + 4 ≤ o → o + 4 ≤ numAt len 4 → w32 u.mem base o = w32 s.mem base o
  up : ∀ o, numAt len 4 + 4 * wp len ≤ o → o + 4 ≤ numAt len 5 → w32 u.mem base o = w32 s.mem base o
  cnt : w32 u.mem base oSteps = nSteps len - i
  x : val32 u.mem base (numAt len 4) (wp len) = 2 ^ (32 * (wp len - 1 + i)) % m

/-- What the steps need of the state `s` before `count`: the header's `p = 2^z`,
`d`, `d₁` and `v`, `M` over `W'` words and `x = 2^(32 (W' - 1)) < M`. -/
structure LoopPre (s : State) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (m z : Nat) : Prop where
  pi : PcIn base bytes len args s
  hz : z ≤ 31
  hP : w32 s.mem base oP = 2 ^ z
  hMw : m * 2 ^ z < 2 ^ (32 * wp len)
  hD : w32 s.mem base oD = m * 2 ^ z / 2 ^ (32 * (wp len - 1))
  hd1 : 2 ^ 31 ≤ m * 2 ^ z / 2 ^ (32 * (wp len - 1))
  hD1 : w32 s.mem base oD1 = m * 2 ^ z / 2 ^ (32 * (wp len - 2)) % 2 ^ 32
  hV : w32 s.mem base oV = (2 ^ 64 - 1) / (m * 2 ^ z / 2 ^ (32 * (wp len - 1))) - 2 ^ 32
  hM : val32 s.mem base (numAt len 0) (wp len) = m
  hx : val32 s.mem base (numAt len 4) (wp len) = 2 ^ (32 * (wp len - 1))
  hxm : 2 ^ (32 * (wp len - 1)) < m

theorem nSteps_pos {len : Nat} (hl : 64 ≤ len) (hu : len ≤ 1024) : 1 ≤ nSteps len := by
  simp only [nSteps, wp, wb, Spec.Rsa.modulusWords]; omega

/-- `count`, from `s`: no steps yet. -/
theorem count_start {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {m z : Nat}
    (L : LoopPre s base bytes len args m z) :
    WP isa (.block count) s fun u => StI s base bytes len args m 0 u := by
  have h := L.pi
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  refine WP.mono (count_ok h) fun u ⟨mu, Ku⟩ => ?_
  have Ou := writeW32_outside s.mem base (d := oSteps) (BitVec.ofNat 32 (nSteps len)) (by simp only [oSteps]; omega_using [])
  rw [← mu] at Ou
  refine ⟨h.keep Ku (by decide) (by decide) (Ou.mono (by omega_using []) (by simp only [oSteps]; omega_using [f5, e5])), Ku.mono (by decide),
    Ou.mono (by simp only [oMask, oSteps]; omega_using []) (by simp only [oMask, oSteps]; omega_using [e5]),
    fun o h1 h2 => Ou.w32 (.inr (by simp only [oU2, oSteps] at *; omega_using [h1])) (by omega_using [nw, f5, e4, h2]),
    fun o h1 h2 => Ou.w32 (.inr (by simp only [oSteps]; omega_using [e4, h1])) (by omega_using [nw, f5, h2]), ?_, ?_⟩
  · rw [Nat.sub_zero, mu, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [nSteps]; omega_using [nw, f5])]
  · rw [Ou.val32 (.inr (by simp only [oSteps]; omega_using [e4])) (by omega_using [nw, f5, hwp, e4]), L.hx, Nat.add_zero, Nat.mod_eq_of_lt L.hxm]

/-- A step and the count down. -/
theorem stepIter_ok {s u : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {m z i : Nat}
    (L : LoopPre s base bytes len args m z) (hi : i < nSteps len) (I : StI s base bytes len args m i u) :
    WP isa (.seq step (.block [.mov .eax (.mem (hd oSteps)), .alu .sub .eax (.imm 1), .store (hd oSteps) .eax])) u
      fun v => StI s base bytes len args m (i + 1) v ∧ v.zf = some (decide (i + 1 = nSteps len)) := by
  have h := L.pi
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have hl := h.lower
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  -- The header and `M` as in `s`.
  have hdr : ∀ o, o + 4 ≤ oMask → w32 u.mem base o = w32 s.mem base o := fun o ho =>
    I.out.w32 (.inl ho) (by simp only [oMask] at ho; omega_using [ho])
  have hMu : val32 u.mem base (numAt len 0) (wp len) = m := by
    rw [← L.hM]; exact val32_congr fun j hj => I.mid _ (by simp only [oU2]; omega_using [e0]) (by omega_using [hwp, e0, e4, hj])
  refine WP.seq (WP.mono (step_ok I.pi L.hz (by rw [hdr _ (by decide)]; exact L.hP) L.hMw
    (by rw [hdr _ (by decide)]; exact L.hD) L.hd1
    (by rw [I.mid _ (by simp only [oD1, oU2]; omega_using []) (by simp only [oD1]; omega_using [e4])]; exact L.hD1)
    (by rw [hdr _ (by decide)]; exact L.hV) hMu I.x
    (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) L.hxm))) fun v ⟨hxv, F, Kv⟩ => ?_)
  have hv := I.pi.keep Kv (by decide) (by decide) (F.out.mono (by omega_using []) (by simp only [oMask]; omega_using [f5, hwp, e5]))
  have ws : Ws v base bytes := hv.ws
  have di : PtrAt v base .edi 0 := by rw [PtrAt, Nat.add_zero, Nat.mod_eq_of_lt (by omega_using [nw, f5])]; exact hv.edi
  have rd := readSrc_ptr ws di (d := oSteps) (by simp only [oSteps]; omega_using [f5, e5])
  rw [Nat.zero_add] at rd
  refine wp_movS rd fun v₁ V₁ _ => wp_subZ rfl fun v₂ V₂ z₂ => ?_
  have K₂ : Keeps k6 v v₂ := (V₁.keeps.mono (by decide)).trans (V₂.keeps.mono (by decide))
  have ws₂ : Ws v₂ base bytes := ws.of_wr K₂.2.2
  have di₂ : PtrAt v₂ base .edi 0 := by rw [PtrAt, K₂.1 _ (by decide)]; exact di
  refine wp_storeS (ea_ptr ws₂ di₂ (d := oSteps) (by simp only [oSteps]; omega_using [f5, e5]))
    (ws_write ws₂ (by simp only [oSteps]; omega_using [f5, e5])) fun t M => WP.block_nil ?_
  have cv : w32 v.mem base oSteps = nSteps len - i := by rw [F.steps]; exact I.cnt
  obtain ⟨c₁, c₂⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf (N := nSteps len) (x := v₁.gpr .eax)
    (by rw [V₁.gpr]; exact cv) hi
  have mt : t.mem = v.mem.writeW (off base oSteps) (v₁.gpr .eax - 1) := by
    rw [M.mem, V₂.mem, V₁.mem, Nat.zero_add, V₂.gpr]
  have Ot := writeW32_outside v.mem base (d := oSteps) (v₁.gpr .eax - 1) (by simp only [oSteps]; omega_using [])
  rw [← mt] at Ot
  refine ⟨⟨hv.keep (K₂.trans (M.keeps _)) (by decide) (by decide) (Ot.mono (by omega_using []) (by simp only [oSteps]; omega_using [f5, e5])),
    I.keep.trans (Kv.trans (K₂.trans (M.keeps _))),
    (I.out.trans F.out).trans (Ot.mono (by simp only [oMask, oSteps]; omega_using []) (by simp only [oMask, oSteps]; omega_using [e5])),
    fun o h1 h2 => ?_, fun o h1 h2 => ?_, ?_, ?_⟩, ?_⟩
  · rw [Ot.w32 (.inr (by simp only [oU2, oSteps] at *; omega_using [h1])) (by omega_using [nw, f5, e4, h2]), F.mid o h1 h2, I.mid o h1 h2]
  · rw [Ot.w32 (.inr (by simp only [oSteps]; omega_using [e4, h1])) (by omega_using [nw, f5, h2]), F.up o h1 h2, I.up o h1 h2]
  · rw [mt, w32_write_self, c₁]
  · rw [Ot.val32 (.inr (by simp only [oSteps]; omega_using [e4])) (by omega_using [nw, f5, hwp, e4]), hxv, Nat.mod_mul_mod, ← Nat.pow_add,
      show 32 * (wp len - 1 + i) + 32 = 32 * (wp len - 1 + (i + 1)) by omega_using []]
  · rw [M.zf, z₂, c₂]

/-- The steps' loop: `S` steps. -/
theorem stepLoop_ok {s u : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {m z : Nat}
    (L : LoopPre s base bytes len args m z) (I : StI s base bytes len args m 0 u) :
    WP isa stepLoop u fun t => StI s base bytes len args m (nSteps len) t :=
  countLoop (nSteps_pos L.pi.lower L.pi.upper) (fun i u => StI s base bytes len args m i u)
    (fun _ _ hi I => stepIter_ok L hi I) I

end VG.Proof.Bignum.X86.R2Words
