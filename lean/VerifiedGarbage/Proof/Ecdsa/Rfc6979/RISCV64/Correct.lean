module

-- separate module: its proofs cost more than its imports, and its importer's changes need
-- not re-check them

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Prep
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.X25519.RISCV64.Instr

/-!
# Deterministic ECDSA on RISC-V: correctness

The function, from the start of the frame's body: the prologue, `X` and `h`,
steps b–g (`Prep.lean`), after which `K` and `V` are RFC 6979's
(`kv0_eq`). Before candidate `i`, they are those of RFC 6979's search
before it (`LoopInv`); a candidate is `T`, the `nV = ⌈Q / D⌉` (`nV_eq`, RFC
6979's number of blocks) `V`s of successive `V = HMAC_K(V)` (`cand_ok`, a
loop, `CI`), whose leftmost `Q` bytes `core` reads as `k`, with `X`'s last
`G` bytes as the digest (`sg_eq`, `coreCall_ok`), then whether to go on
(`goOn_ok`) and step h.3 or the end (`tryOne_ok`, `loop_ok`). The candidate
the loop stops at has RFC 6979's signature (`result_eq`). In its frame, the
function meets `rfcRC` (`correct`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li wp_add wp_sltu)
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)

variable {P : Rfc}

/-! ## The candidate -/

/-- `genT` with one more `V`: the last after the others. -/
theorem genT_succ (H : Spec.Hmac.HashFunction) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    Spec.Ecdsa.Rfc6979.genT H K (k + 1) V =
      ((Spec.Ecdsa.Rfc6979.genT H K k V).1 ++ Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2)
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    show (Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).1,
        (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).2) =
      ((Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).1) ++
          Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2)
    rw [genT_succ H K k (Spec.Hmac.hmac H K V)]
    simp

theorem mac_length (P : Rfc) (K t : List Byte) : (Spec.Hmac.hmac P.hH.SH.H K t).length = P.H.D := by
  simp only [Spec.Hmac.hmac]
  exact P.hH.hashLen _

theorem genT_length (P : Rfc) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K k V).1.length = k * P.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    rw [genT_succ, List.length_append, genT_length P K k V, mac_length]
    rw [Nat.succ_mul]

/-- The number of `V`s in a candidate: `⌈Q / D⌉`. -/
abbrev Rfc.nV (P : Rfc) : Nat := (P.Q + P.H.D - 1) / P.H.D

theorem nV_lt (P : Rfc) (j : Nat) : j + 1 < P.nV ↔ (j + 1) * P.H.D < P.Q := by
  have := (sizes P).D
  rw [Rfc.nV, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), Nat.succ_mul (j + 1)]
  omega

theorem nV_facts (P : Rfc) : 1 ≤ P.nV ∧ P.nV * P.H.D ≤ P.Q + P.H.D - 1 ∧ P.Q ≤ P.nV * P.H.D := by
  have := (sizes P).D
  have := (sizes P).Q
  have e₁ := Nat.div_mul_le_self (P.Q + P.H.D - 1) P.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.H.D - 1) (show 0 < P.H.D by omega)
  have e₃ : 1 ≤ P.nV := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  simp only [Rfc.nV] at e₃ ⊢
  generalize (P.Q + P.H.D - 1) / P.H.D = N at e₁ e₂ e₃ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  omega

/-- RFC 6979's number of blocks is `⌈Q / D⌉`. -/
theorem nV_eq (P : Rfc) : Spec.Ecdsa.Rfc6979.blocks P.kit.E.curve P.H.D = P.nV := by
  have := (sizes P).D
  have := (sizes P).Q
  have hl := P.kit.nbits
  have hsh := P.kit.sh8
  have e₁ := Nat.div_mul_le_self (P.Q + P.H.D - 1) P.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.H.D - 1) (show 0 < P.H.D by omega)
  rw [Spec.Ecdsa.Rfc6979.blocks]
  simp only [Rfc.nV, Rfc.Q] at e₁ e₂ hl ⊢
  generalize (P.kit.Q + P.H.D - 1) / P.H.D = N at e₁ e₂ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  have h₁ : N * (8 * P.H.D) = 8 * (N * P.H.D) := Nat.mul_left_comm _ _ _
  have h₂ : (N + 1) * (8 * P.H.D) = 8 * (N * P.H.D) + 8 * P.H.D := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- After `j` `V`s of the candidate, from `K` and `V₀`: `V`, `T` and its
length, and `s5` as at the start (`c`). -/
structure CI (P : Rfc) (s₀ : State) (K V₀ : List Byte) (c : BitVec 64) (j : Nat) (u : State) : Prop where
  kvh : KVH P s₀ K (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K j V₀).2 u
  s9 : u.gpr .s9 = BitVec.ofNat 64 (j * P.H.D)
  T : bytesAt u.mem (sA s₀ fT) (j * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K j V₀).1
  s5 : u.gpr .s5 = c
  sy : u.syms = s₀.syms

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- One `V` of the candidate. -/
theorem candStep_ok {K V₀ : List Byte} {c : BitVec 64} {j : Nat} {u : State} (hj : j < P.nV)
    (hI : CI P s₀ K V₀ c j u) :
    WP isa P.c.candStep u fun w => CI P s₀ K V₀ c (j + 1) w ∧
      isa.eval (.nonzero .t6) w = some (decide (j + 1 < P.nV)) := by
  have hz := sizes P
  obtain ⟨hQ1, hQ2, hcQ, -⟩ := hz.Q
  obtain ⟨hD0, hD⟩ := hz.D
  have hfr : frB = 512 := rfl
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  have hjD : (j + 1) * P.H.D ≤ 136 := by
    have : j + 1 ≤ P.nV := hj
    have := Nat.mul_le_mul_right P.H.D this
    omega
  have hjD' : j * P.H.D + P.H.D ≤ 136 := by rw [Nat.succ_mul] at hjD; exact hjD
  have e₂ : (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K (j + 1) V₀).2 =
      Spec.Hmac.hmac P.hH.SH.H K (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K j V₀).2 := by rw [genT_succ]
  have e₁ : (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K (j + 1) V₀).1 = (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K j V₀).1 ++
      Spec.Hmac.hmac P.hH.SH.H K (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K j V₀).2 := by rw [genT_succ]
  unfold Cfg.candStep
  refine VG.RISCV64.WP.of_syms ?_
  refine WP.seq (VG.RISCV64.WP.mono_syms (hmacV_ok hp hI.kvh hI.sy) fun u₁ ⟨k₁, pr₁, f₁⟩ y₁ => ?_)
  rw [← e₂] at k₁
  have s9₁ : u₁.gpr .s9 = BitVec.ofNat 64 (j * P.H.D) := by rw [pr₁ _ (by decide), hI.s9]
  have s5₁ : u₁.gpr .s5 = c := by rw [pr₁ _ (by decide), hI.s5]
  have T₁ : bytesAt u₁.mem (sA s₀ fT) (j * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K j V₀).1 := by
    rw [← hI.T]
    exact fbytes f₁ (hd_apart hp (by simp only [fT]; omega) (.inr (by simp only [fV, fT]; omega))
      (by simp only [fV]; omega)) (by omega)
  -- `V` to `T + |T|`
  refine WP.seq (wp_addi (by simp only [fV]; omega) fun u₂ v₂ => wp_addi (by simp only [fT]; omega)
    fun u₃ v₃ => wp_add fun u₄ v₄ => wp_mv fun u₅ v₅ => WP.block_nil ?_)
  have k₅ : KR P s₀ u₅ := (((k₁.kr.upd (by decide) v₂).upd (by decide) v₃).upd (by decide) v₄).upd (by decide) v₅
  have m₅ : u₅.mem = u₁.mem := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem]
  have a4 : u₅.gpr .a4 = sA s₀ fV := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, k₁.kr.s1]
  have a5 : u₅.gpr .a5 = sA s₀ (fT + j * P.H.D) := by
    rw [v₅.other _ (by decide), v₄.gpr, v₃.gpr, v₃.other .s9 (by decide), v₂.other .s1 (by decide),
      v₂.other .s9 (by decide), k₁.kr.s1, s9₁, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have a6 : u₅.gpr .a6 = BitVec.ofNat 64 P.H.D := by
    rw [v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), k₁.kr.s7]
  have s9₅ : u₅.gpr .s9 = BitVec.ofNat 64 (j * P.H.D) := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), s9₁]
  have s5₅ : u₅.gpr .s5 = c := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), s5₁]
  have rd₅ := k₅.rd
  have wr₅ := k₅.wr
  refine WP.seq (WP.mono (WP.rdwr (copyLoop_adv (tmp := .t1) (src := .a4) (dst := .a5) (cnt := .a6) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) u₅ hD0 (by omega) a6
    (fun i hi => by
      rw [a4, add_ofNat_add']
      exact in_fr' hp wr₅ (o := fV + i) (n := 1) (by simp only [fV]; omega))
    (fun i hi => by
      rw [a5, add_ofNat_add']
      exact in_fr hp wr₅ (o := fT + j * P.H.D + i) (n := 1) (by simp only [fT]; omega))
    (fun x hx hx' => by
      rw [a5] at hx
      rw [a4] at hx'
      exact part_disj (s₀ := s₀) (a := fT + j * P.H.D) (m := P.H.D) (b := fV) (n := P.H.D)
        (.inr (by simp only [fV, fT]; omega)) (by simp only [fT]; omega) (by simp only [fV]; omega) x hx hx')))
    fun w ⟨⟨hc, hf, hk, _⟩, hrd, hwr, hsp⟩ => ?_)
  rw [a5] at hc hf
  rw [a4] at hc
  have kw : KR P s₀ w := k₅.keep hrd hwr hsp (fun r hr => hk.gpr (by revert r; decide)) hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by simp only [fT]; omega)) (by decide) (by simp only [fT]; omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, part_sub (by simp only [fT]; omega)⟩)
  have ap : ∀ {o n : Nat}, (o + n ≤ fT + j * P.H.D ∨ fT + j * P.H.D + P.H.D ≤ o) → o + n ≤ frB →
      ∀ r ∈ [sR s₀ (fT + j * P.H.D) P.H.D], Region.Disjoint (sR s₀ o n) r := fun ho ho' r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact part_disj ho (by omega) (by simp only [fT]; omega)
  refine wp_add fun x₁ q₁ => wp_li (imm := P.c.Q) (by omega) fun x₂ q₂ => wp_sltu fun x₃ q₃ => WP.block_nil fun syx => ?_
  have kx : KR P s₀ x₃ := ((kw.upd (by decide) q₁).upd (by decide) q₂).upd (by decide) q₃
  have mx : x₃.mem = w.mem := by rw [q₃.mem, q₂.mem, q₁.mem]
  have s9x : x₃.gpr .s9 = BitVec.ofNat 64 ((j + 1) * P.H.D) := by
    rw [q₃.other _ (by decide), q₂.other _ (by decide), q₁.gpr, hk.gpr (by decide), s9₅, kw.s7,
      BitVec.ofNat_add_ofNat, Nat.succ_mul]
  refine ⟨⟨⟨kx, ?_, ?_, ?_, ?_⟩, s9x, ?_, ?_, ?_⟩, ?_⟩
  · rw [mx, ← k₁.k, ← m₅]
    exact fbytes hf (ap (.inl (by simp only [fK, fT]; omega)) (by simp only [fK]; omega)) (by omega)
  · rw [mx, ← k₁.v, ← m₅]
    exact fbytes hf (ap (.inl (by simp only [fV, fT]; omega)) (by simp only [fV]; omega)) (by omega)
  · rw [mx, ← k₁.h, ← m₅]
    have := fHo_in P
    exact fbytes hf (ap (.inl (by simp only [fT] at this ⊢; omega)) (by simp only [fT] at this; omega)) (by omega)
  · rw [mx, ← k₁.x, ← m₅]
    exact fbytes hf (ap (.inl (by simp only [fX, fT]; omega)) (by simp only [fX]; omega)) (by omega)
  · rw [mx, Nat.succ_mul, VG.Proof.Hmac.Common.bytesAt_add, add_ofNat_add', e₁,
      fbytes hf (ap (.inl (Nat.le_refl _)) (by simp only [fT]; omega)) (by omega), m₅, T₁]
    congr 1
    rw [← e₂, ← k₁.v]
    apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.length_map, List.length_range] at h₁ ⊢
    rw [add_ofNat_add', ← add_ofNat_add', hc i h₁, m₅]
  · rw [q₃.other _ (by decide), q₂.other _ (by decide), q₁.other _ (by decide), hk.gpr (by decide), s5₅]
  · exact syx.trans hI.sy
  · rw [VG.RISCV64.Steps.eval_nonzero, q₃.gpr, q₂.gpr, q₂.other _ (by decide), q₁.gpr, hk.gpr (by decide), s9₅,
      kw.s7, BitVec.ofNat_add_ofNat, hcQ]
    have hlt : (BitVec.ofNat 64 (j * P.H.D + P.H.D) < BitVec.ofNat 64 P.Q) = (j * P.H.D + P.H.D < P.Q) := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have hn := nV_lt P j
    rw [Nat.succ_mul] at hn
    by_cases h' : j * P.H.D + P.H.D < P.Q
    · rw [ite_eq_left (by rw [hlt]; exact h'), decide_eq_true (hn.mpr h')]; rfl
    · rw [ite_eq_right (by rw [hlt]; exact h'), decide_eq_false (fun h'' => h' (hn.mp h''))]; rfl

end

end VG.Proof.Ecdsa.Rfc6979.RISCV64
