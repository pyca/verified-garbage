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

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- The candidate: `nV` `V`s of successive `V = HMAC_K(V)`. -/
theorem cand_ok {K V₀ : List Byte} {t : State} (h : KVH P s₀ K V₀ t) (hsy : t.syms = s₀.syms) :
    WP isa P.c.cand t fun w => KVH P s₀ K (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K P.nV V₀).2 w ∧
      bytesAt w.mem (sA s₀ fT) (P.nV * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K P.nV V₀).1 ∧
      w.gpr .s5 = t.gpr .s5 ∧ w.syms = s₀.syms := by
  obtain ⟨hN1, -, -⟩ := nV_facts P
  unfold Cfg.cand Cfg.tInit
  refine WP.seq (VG.RISCV64.WP.of_syms (wp_li (imm := 0) (by decide) fun t₁ u₁ => WP.block_nil fun y₁ => ?_))
  have I₀ : CI P s₀ K V₀ (t.gpr .s5) 0 t₁ :=
    ⟨⟨h.kr.upd (by decide) u₁, by rw [u₁.mem]; exact h.k, by rw [u₁.mem]; exact h.v, by rw [u₁.mem]; exact h.h,
      by rw [u₁.mem]; exact h.x⟩, by rw [u₁.gpr, Nat.zero_mul], by simp [bytesAt, Spec.Ecdsa.Rfc6979.genT],
      u₁.other _ (by decide), y₁.trans hsy⟩
  refine WP.loop (M := isa) (fun n u => ∃ j, n = P.nV - j ∧ j < P.nV ∧ CI P s₀ K V₀ (t.gpr .s5) j u) ?_ _ t₁
    ⟨0, rfl, hN1, I₀⟩
  rintro n u ⟨j, rfl, hj, hI⟩
  refine WP.mono (candStep_ok hp hj hI) fun w ⟨hw, he⟩ => ?_
  by_cases hg : j + 1 < P.nV
  · exact .inr ⟨by rw [he, decide_eq_true hg], _, by omega, j + 1, rfl, hg, hw⟩
  · have e : j + 1 = P.nV := by omega
    rw [e] at hw
    exact .inl ⟨by rw [he, decide_eq_false hg], hw.kvh, hw.T, hw.s5, hw.sy⟩

end

/-! ## The candidates' signatures -/

/-- `K` and `V` after steps b–g, before candidate `i`, candidate `i`'s `T`,
and its signature. -/
abbrev kv0 (P : Rfc) (s₀ : State) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.kit.E.curve P.hH.SH.H P.H.D (xOf P s₀) (hBOf P s₀)
abbrev kvI (P : Rfc) (s₀ : State) (i : Nat) : List Byte × List Byte :=
  VG.Proof.Ecdsa.Rfc6979.kvAtB P.hH.SH.H P.nV (kv0 P s₀).1 (kv0 P s₀).2 i
abbrev candI (P : Rfc) (s₀ : State) (i : Nat) : List Byte :=
  VG.Proof.Ecdsa.Rfc6979.candAtB P.hH.SH.H P.nV (kv0 P s₀).1 (kv0 P s₀).2 i
abbrev sigI (P : Rfc) (s₀ : State) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.kit.E.curve (xOf P s₀) (eOf P s₀) (Spec.Ecdsa.Rfc6979.bits2int P.kit.E.curve (candI P s₀ i))

/-- Before candidate `i`. -/
structure LoopInv (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop where
  lt : i < P.c.tries
  kvh : KVH P s₀ (kvI P s₀ i).1 (kvI P s₀ i).2 t
  cnt : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)
  fails : ∀ j < i, sigI P s₀ j = none
  sy : t.syms = s₀.syms

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : Rfc) (s₀ : State) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => t.gpr .a0 = 1 ∧ bytesAt t.mem (out s₀) (2 * P.Q) = Spec.Ecdsa.encode P.kit.E.curve rs
  | none => t.gpr .a0 = 0 ∧ bytesAt t.mem (out s₀) (2 * P.Q) = List.replicate (2 * P.Q) 0

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop where
  lt : i < P.c.tries
  kr : KR P s₀ t
  fails : ∀ j < i, sigI P s₀ j = none
  last : sigI P s₀ i ≠ none ∨ i + 1 = P.c.tries
  res : ResultIs P s₀ (sigI P s₀ i) t

theorem ResultIs.keep {P : Rfc} {s₀ : State} {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P s₀ r t)
    (ha : t'.gpr .a0 = t.gpr .a0) (hm : bytesAt t'.mem (out s₀) (2 * P.Q) = bytesAt t.mem (out s₀) (2 * P.Q)) :
    ResultIs P s₀ r t' := by
  unfold ResultIs at *
  split at h <;> exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- What `core` reads is candidate `i`'s signature's input: the digest, `X`'s
last `G` bytes, and `k`, `T`'s first `Q`. -/
theorem sg_eq {t : State} (hk : KR P s₀ t) (hx : xOfM P s₀ t.mem = xSpec P s₀) {i : Nat}
    (hT : bytesAt t.mem (sA s₀ fT) (P.nV * P.H.D) = candI P s₀ i) :
    sgOf P.kit.E P.Q P.kit.G P.kit.sh t.mem (dk s₀) (sA s₀ P.c.fDg) (sA s₀ fT) = sigI P s₀ i := by
  have hz := sizes P
  obtain ⟨hQ1, hQ2, hcQ, -⟩ := hz.Q
  obtain ⟨hD0, hD⟩ := hz.D
  obtain ⟨-, -, hNQ⟩ := nV_facts P
  have hnb : Spec.Ecdsa.nBits P.kit.E.curve + P.kit.sh = 8 * P.Q := P.kit.nbits
  have hsh := P.kit.sh8
  have hG := hz.G
  have hGQ : P.kit.G ≤ P.Q := by
    cases hb : P.c.big
    · rw [hG.2.2 hb]
    · rw [hG.2.1 hb]; have := hz.big.1.mp hb; omega
  have hfDg : P.c.fDg = fX + (P.Q - P.kit.G) := by rw [Cfg.fDg, hcQ, hG.1]
  -- `X`'s last `G` bytes
  have hX : bytesAt t.mem (sA s₀ P.c.fDg) P.kit.G = (xSpec P s₀).drop (P.Q - P.kit.G) := by
    have e := VG.Proof.Hmac.Common.bytesAt_add t.mem (sA s₀ fX) (P.Q - P.kit.G) P.kit.G
    rw [Nat.sub_add_cancel hGQ] at e
    rw [← hx, xOfM, e, List.drop_left' (bytesAt_length _ _ _), add_ofNat_add', hfDg]
  simp only [sgOf, sigI]
  congr 1
  · exact congrArg _ (hk.dBytes hp)
  · rw [hX]
    cases hb : P.c.big
    · have hG' := hG.2.2 hb
      have hsh0 := P.hsh hb
      rw [hG', Nat.sub_self, List.drop_zero]
      have hq : Spec.Ecdsa.nBits P.kit.E.curve = 8 * P.Q := by rw [hsh0] at hnb; omega
      have hl : (xSpec P s₀).length = P.Q := by
        simp only [xSpec, List.length_append, List.length_replicate, List.length_take, bytesAt_length]; omega
      rw [Spec.Ecdsa.hashToInt, ite_eq_left (by rw [hl, hq])]
      exact x_eq hq (n_ne P) (bytesAt_length _ _ _)
    · have hG' := hG.2.1 hb
      have hQb := hz.big.1.mp hb
      rw [hG']
      have e : (xSpec P s₀).drop (P.Q - 64) = List.replicate (64 - P.H.D) 0 ++ hBOf P s₀ := by
        simp only [xSpec, Nat.min_eq_left (show P.H.D ≤ P.Q by omega),
          List.take_of_length_le (show (hBOf P s₀).length ≤ P.H.D by rw [bytesAt_length])]
        rw [List.drop_append, List.drop_replicate, List.length_replicate,
          show P.Q - 64 - (P.Q - P.H.D) = 0 by omega, List.drop_zero, show P.Q - P.H.D - (P.Q - 64) = 64 - P.H.D by omega]
      have hl : (List.replicate (64 - P.H.D) (0 : Byte) ++ hBOf P s₀).length = 64 := by
        simp only [List.length_append, List.length_replicate, bytesAt_length]; omega
      have hlB : (hBOf P s₀).length = P.H.D := bytesAt_length _ _ _
      rw [e, Spec.Ecdsa.hashToInt, ite_eq_left (by rw [hl]; omega), VG.Proof.Ecdsa.Rfc6979.ofBytes_zeros]
      show _ = Spec.Ecdsa.hashToInt _ (hBOf P s₀)
      rw [(VG.Proof.Ecdsa.Rfc6979.hashToInt_short (by rw [hlB]; omega) (n_ne P)).1]
  · rw [Spec.Ecdsa.Rfc6979.bits2int, VG.Proof.Ecdsa.Rfc6979.hashToInt_takeR (R := P.Q) (by omega)
      (by rw [← hT, bytesAt_length]; exact hNQ), ← hT, ← bytesAt_take _ _ hNQ,
      show 8 * P.Q - Spec.Ecdsa.nBits P.kit.E.curve = P.kit.sh by omega]

end

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- The tables are kept: the code writes only `wrs`. -/
theorem held_of {t : State} (hk : KR P s₀ t) : Abi.constsHeld t.mem (fun name => s₀.syms name) P.kit.K :=
  fun c hc i hi => by
  rw [← hp.held c hc i hi]
  have hr : (⟨s₀.syms c.1, 8 * c.2.length⟩ : Region) ∈ constRegs P.kit.K s₀ := List.mem_map_of_mem hc
  have := hp.tfit _ hr
  refine Mem.readW_congr fun b hb => hk.frame _ fun r hr' hc' => hp.t_w _ hr r hr' _ ?_ hc'
  simp only [Region.Contains] at this ⊢
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Mem.sub_ofNat_toNat _ (by omega)]
  omega

/-- `core`'s arguments: `X`'s last `G` bytes as the digest, `T` as `k`. -/
theorem coreArgs_ok {t : State} {K V : List Byte} (h : KVH P s₀ K V t) (hsy : t.syms = s₀.syms) :
    WP isa (.block P.c.coreArgs) t fun u =>
      KVH P s₀ K V u ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧ u.mem = t.mem ∧
      CoreArgsG P.Q P.kit.G P.kit.K u (out s₀) (dk s₀) (sA s₀ P.c.fDg) (sA s₀ fT) (scr s₀) := by
  have hz := sizes P
  obtain ⟨hQ1, hQ2, hcQ, -⟩ := hz.Q
  have hfr : frB = 512 := rfl
  have hG := hz.G
  have hGQ : P.kit.G ≤ P.Q := by
    cases hb : P.c.big
    · rw [hG.2.2 hb]
    · rw [hG.2.1 hb]; have := hz.big.1.mp hb; omega
  have hfDg : P.c.fDg = fX + (P.Q - P.kit.G) := by rw [Cfg.fDg, hcQ, hG.1]
  have hdg : P.c.fDg + P.kit.G ≤ fT := by rw [hfDg]; simp only [fX, fT]; omega
  have hfT : fT = 368 := rfl
  have hfX : fX = 232 := rfl
  unfold Cfg.coreArgs
  refine VG.RISCV64.WP.of_syms (wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (by simp only [fT] at hdg; omega)
    fun s₃ u₃ => wp_addi (by simp only [fT]; omega) fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil fun sy₅ => ?_)
  have mm : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₅ : KR P s₀ s₅ := (((((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd
    (by decide) u₄).upd (by decide) u₅)
  have ef : (fun name => s₅.syms name) = fun name => s₀.syms name := by rw [sy₅, hsy]
  have cr : constRegs P.kit.K s₅ = constRegs P.kit.K s₀ := by simp only [constRegs, ef]
  have kS : Region.Sub ⟨sA s₀ fT, P.Q⟩ (frR s₀) := part_sub (by simp only [fT]; omega)
  have gS : Region.Sub ⟨sA s₀ P.c.fDg, P.kit.G⟩ (frR s₀) := part_sub (by simp only [fT] at hdg; omega)
  have hn : ∀ o, o ≤ frB → (sA s₀ o).toNat + (frB - o) ≤ 2 ^ 64 := fun o ho => by
    have := hp.top
    show (s₀.sp + BitVec.ofNat 64 o).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨⟨k₅, by rw [mm]; exact h.k, by rw [mm]; exact h.v, by rw [mm]; exact h.h, by rw [mm]; exact h.x⟩,
    fun r hr => ?_, mm, ?_, ?_, ?_, ?_, ?_,
    hp.o_c, hp.d_c, hp.f_c.sub_left gS, hp.f_c.sub_left kS, hp.no, hp.nd,
    by have := hn P.c.fDg (by simp only [fT] at hdg; omega); omega, by have := hn fT (by decide); omega,
    hp.nc, hp.ca, by rw [mm, ef]; exact held_of hp h.kr,
    by rw [cr]; exact hp.tfit, by rw [cr]; exact hp.tal,
    fun r hr => hp.t_w r (by rwa [cr] at hr) _ (by simp),
    fun r hr => hp.t_w r (by rwa [cr] at hr) _ (by simp), ?_, ?_⟩
  · rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
      u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    exact h.kr.s2
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    exact h.kr.s3
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s1]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s1]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    exact h.kr.s0
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (((rfl | rfl | rfl) | hr) | rfl | rfl)
    · exact ⟨dR P s₀, List.mem_append_left _ (by rw [k₅.rd, hp.rd]; simp), 0, by simp, by simp⟩
    · exact cov_fr hp k₅ (o := P.c.fDg) (n := P.kit.G) (by simp only [fT] at hdg; omega)
    · exact cov_fr hp k₅ (o := fT) (n := P.Q) (by simp only [fT]; omega)
    · exact ⟨r, List.mem_append_left _ (by rw [k₅.rd, hp.rd, ← cr]; exact List.mem_append_right _ hr), 0,
        by simp, by simp⟩
    · exact ⟨outR P s₀, List.mem_append_right _ (out_wr hp k₅.wr), 0, by simp, by simp⟩
    · exact cov_scr hp k₅ (o := 0) (n := 8192) (by decide) |>.imp fun r' ⟨hm, off, hb, hl⟩ =>
        ⟨hm, off, by rw [← hb]; simp, hl⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨outR P s₀, out_wr hp k₅.wr, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, scr_wr hp k₅.wr, 0, by simp, by simp⟩

/-- `core` with candidate `i`. -/
theorem coreCall_ok {t : State} {K V : List Byte} (h : KVH P s₀ K V t) {i : Nat}
    (hsg : sgOf P.kit.E P.Q P.kit.G P.kit.sh t.mem (dk s₀) (sA s₀ P.c.fDg) (sA s₀ fT) = sigI P s₀ i)
    (ha : CoreArgsG P.Q P.kit.G P.kit.K t (out s₀) (dk s₀) (sA s₀ P.c.fDg) (sA s₀ fT) (scr s₀)) :
    WP isa (.call P.c.coreN P.c.coreC) t fun u => KVH P s₀ K V u ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      ResultIs P s₀ (sigI P s₀ i) u := by
  have hz := sizes P
  have hfr : frB = 512 := rfl
  rw [P.hcC]
  refine P.kit.core_call ha fun u a hpost => ?_
  have hw : ∀ r ∈ [(⟨out s₀, 2 * P.Q⟩ : Region), ⟨scr s₀, 8192⟩], Wk P s₀ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl fun x hx => hx)
    · exact .inr (.inr (.inl fun x hx => hx))
  have kp : ∀ {o n : Nat}, o + n ≤ frB → ∀ r ∈ [(⟨out s₀, 2 * P.Q⟩ : Region), ⟨scr s₀, 8192⟩],
      Region.Disjoint (sR s₀ o n) r := fun ho r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.f_o.sub_left (part_sub ho)
    · exact hp.f_c.sub_left (part_sub ho)
  have := fHo_in P
  have := hz.Q
  have := hz.D
  have hfT : fT = 368 := rfl
  have hfX : fX = 232 := rfl
  refine ⟨⟨h.kr.call hp a.rd a.wr a.sp a.cs a.frame hw, ?_, ?_, ?_, ?_⟩, a.cs, ?_⟩
  · rw [← h.k]; exact fbytes a.frame (kp (by have := hz.D; simp only [fK]; omega)) (by omega)
  · rw [← h.v]; exact fbytes a.frame (kp (by have := hz.D; simp only [fV]; omega)) (by omega)
  · rw [← h.h]; exact fbytes a.frame (kp (by simp only [fT] at *; omega)) (by omega)
  · rw [← h.x]; exact fbytes a.frame (kp (by simp only [fX]; omega)) (by omega)
  · rw [hsg] at hpost
    unfold ResultIs
    exact hpost

end

/-! ## One candidate, and the loop -/

theorem sub_one_ofNat {k : Nat} (h₁ : 1 ≤ k) (h₂ : k < 2 ^ 64) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem nonzero_ofNat {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  rw [bne, VG.RISCV64.Steps.ofNat_beq_zero h]
  simp

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
/-- One candidate fewer, and whether to go on. -/
theorem goOn_ok {t : State} {K V : List Byte} (h : KVH P s₀ K V t) {i : Nat} (hi : i < P.c.tries)
    (hc : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)) (hr : ResultIs P s₀ (sigI P s₀ i) t) :
    WP isa (.block Cfg.goOn) t fun u => KVH P s₀ K V u ∧ ResultIs P s₀ (sigI P s₀ i) u ∧
      u.gpr .s5 = BitVec.ofNat 64 (P.c.tries - (i + 1)) ∧
      isa.eval (.nonzero .t6) u = some (decide (sigI P s₀ i = none ∧ i + 1 < P.c.tries)) := by
  have hT := P.hT'
  unfold Cfg.goOn
  refine VG.RISCV64.Steps.wp_subi (imm := 1) (by decide) fun s₁ u₁ =>
    VG.RISCV64.Steps.wp_andi (imm := 1) (by decide) fun s₂ u₂ =>
    VG.RISCV64.Steps.wp_subi (imm := 1) (by decide) fun s₃ u₃ =>
    VG.Proof.X25519.RISCV64.wp_and fun s₄ u₄ => WP.block_nil ?_
  have mm : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₄ : KR P s₀ s₄ := ((((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄)
  have c₄ : s₄.gpr .s5 = BitVec.ofNat 64 (P.c.tries - (i + 1)) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hc,
      sub_one_ofNat (by omega) (by omega), show P.c.tries - i - 1 = P.c.tries - (i + 1) by omega]
  have a₄ : s₄.gpr .a0 = t.gpr .a0 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have t6 : s₄.gpr .t6 = ((t.gpr .a0 &&& BitVec.ofInt 64 1) - BitVec.ofNat 64 1) &&& s₄.gpr .s5 := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other .a0 (by decide), c₄, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      hc, sub_one_ofNat (by omega) (by omega), show P.c.tries - i - 1 = P.c.tries - (i + 1) by omega]
  refine ⟨⟨k₄, by rw [mm]; exact h.k, by rw [mm]; exact h.v, by rw [mm]; exact h.h, by rw [mm]; exact h.x⟩,
    hr.keep a₄ (by rw [mm]), c₄, ?_⟩
  rw [VG.RISCV64.Steps.eval_nonzero, t6, c₄]
  unfold ResultIs at hr
  split at hr
  · rename_i rs hs
    rw [hr.1, hs]
    have e : ((1 : BitVec 64) &&& BitVec.ofInt 64 1) - BitVec.ofNat 64 1 = 0 := by decide
    rw [e]
    simp
  · rename_i hs
    rw [hr.1, hs]
    have e : ((0 : BitVec 64) &&& BitVec.ofInt 64 1) - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide
    rw [e, BitVec.allOnes_and, nonzero_ofNat (by omega)]
    simp only [true_and]
    congr 1
    exact decide_eq_decide.mpr (by omega)

/-- After `core`: whether to go on, and step h.3 or the end. -/
theorem tryRest_ok {t : State} {i : Nat} (hlt : i < P.c.tries) (hf : ∀ j < i, sigI P s₀ j = none)
    (k₃ : KVH P s₀ (kvI P s₀ i).1
      (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H (kvI P s₀ i).1 P.nV (kvI P s₀ i).2).2 t)
    (c₃ : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)) (r₃ : ResultIs P s₀ (sigI P s₀ i) t)
    (y₃ : t.syms = s₀.syms) :
    WP isa (.seq (.block Cfg.goOn) (.ite (.nonzero .t6) (.seq P.c.rekey (.block Cfg.again)) (.block Cfg.stop))) t
      fun u =>
      isa.eval (.nonzero .t6) u = some (decide (sigI P s₀ i = none ∧ i + 1 < P.c.tries)) ∧
      (sigI P s₀ i = none ∧ i + 1 < P.c.tries → LoopInv P s₀ (i + 1) u) ∧
      (¬ (sigI P s₀ i = none ∧ i + 1 < P.c.tries) → Exit P s₀ i u) := by
  refine WP.seq (VG.RISCV64.WP.mono_syms (goOn_ok k₃ hlt c₃ r₃) fun t₄ ⟨k₄, r₄, c₄, e₄⟩ y₄ => ?_)
  have y₄' : t₄.syms = s₀.syms := y₄.trans y₃
  refine WP.ite _ e₄ (fun hg => ?_) fun hg => ?_
  · obtain ⟨hn, hlt'⟩ := of_decide_eq_true hg
    refine WP.seq (VG.RISCV64.WP.mono_syms (rekey_ok hp k₄ y₄') fun t₅ ⟨k₅, p₅⟩ y₅ => ?_)
    refine VG.RISCV64.WP.of_syms (wp_li (imm := 1) (by decide) fun t₆ u₆ =>
      WP.block_nil fun y₆ => ⟨?_, fun _ => ?_, fun hn' => absurd ⟨hn, hlt'⟩ hn'⟩)
    · rw [VG.RISCV64.Steps.eval_nonzero, u₆.gpr, decide_eq_true ⟨hn, hlt'⟩]; rfl
    · have m₆ : t₆.mem = t₅.mem := u₆.mem
      refine ⟨hlt', ⟨k₅.kr.upd (by decide) u₆, by rw [m₆]; exact k₅.k, by rw [m₆]; exact k₅.v,
        by rw [m₆]; exact k₅.h, by rw [m₆]; exact k₅.x⟩, ?_, fun j hj => ?_, y₆.trans (y₅.trans y₄')⟩
      · rw [u₆.other _ (by decide), p₅ _ (by decide), c₄]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hf j hj
        · exact hn
  · have hl : ¬ (sigI P s₀ i = none ∧ i + 1 < P.c.tries) := of_decide_eq_false hg
    refine wp_li (imm := 0) (by decide) fun t₅ u₅ => WP.block_nil ⟨?_, fun h' => absurd h' hl, fun _ => ?_⟩
    · rw [VG.RISCV64.Steps.eval_nonzero, u₅.gpr, decide_eq_false hl]; rfl
    · refine ⟨hlt, k₄.kr.upd (by decide) u₅, hf, ?_, r₄.keep (u₅.other _ (by decide)) (by rw [u₅.mem])⟩
      by_cases hs : sigI P s₀ i = none
      · have h1 := hlt
        have h2 : ¬ i + 1 < P.c.tries := fun h' => hl ⟨hs, h'⟩
        exact .inr (by omega)
      · exact .inl hs

/-- One candidate: on, before the next, or the end. -/
theorem tryOne_ok {t : State} {i : Nat} (h : LoopInv P s₀ i t) :
    WP isa P.c.tryOne t fun u =>
      isa.eval (.nonzero .t6) u = some (decide (sigI P s₀ i = none ∧ i + 1 < P.c.tries)) ∧
      (sigI P s₀ i = none ∧ i + 1 < P.c.tries → LoopInv P s₀ (i + 1) u) ∧
      (¬ (sigI P s₀ i = none ∧ i + 1 < P.c.tries) → Exit P s₀ i u) := by
  unfold Cfg.tryOne
  refine WP.seq (WP.mono (cand_ok hp h.kvh h.sy) fun t₁ ⟨k₁, T₁, c₁, y₁⟩ => ?_)
  refine WP.seq (VG.RISCV64.WP.mono_syms (coreArgs_ok hp k₁ y₁) fun t₂ ⟨k₂, p₂, m₂, a₂⟩ y₂ => ?_)
  have hT : bytesAt t₂.mem (sA s₀ fT) (P.nV * P.H.D) = candI P s₀ i := by rw [m₂, T₁]; rfl
  refine WP.seq (VG.RISCV64.WP.mono_syms (coreCall_ok hp k₂ (sg_eq hp k₂.kr k₂.x hT) a₂)
    fun t₃ ⟨k₃, p₃, r₃⟩ y₃ => ?_)
  exact tryRest_ok hp h.lt h.fails k₃ (by rw [p₃ _ (by decide), p₂ _ (by decide), c₁, h.cnt]) r₃
    (y₃.trans (y₂.trans y₁))

/-- The candidates, from the first: the loop stops at one. -/
theorem loop_ok {t : State} (h : LoopInv P s₀ 0 t) :
    WP isa (.loop P.c.tryOne (.nonzero .t6)) t fun u => ∃ i, Exit P s₀ i u := by
  refine WP.loop (M := isa) (fun n u => ∃ i, n = P.c.tries - i ∧ LoopInv P s₀ i u) ?_ _ t ⟨0, rfl, h⟩
  rintro n u ⟨i, rfl, hi⟩
  refine WP.mono (tryOne_ok hp hi) fun w ⟨he, hon, hoff⟩ => ?_
  by_cases hg : sigI P s₀ i = none ∧ i + 1 < P.c.tries
  · have hl := hon hg
    exact .inr ⟨by rw [he, decide_eq_true hg], _, by have := hl.lt; omega, i + 1, rfl, hl⟩
  · exact .inl ⟨by rw [he, decide_eq_false hg], i, hoff hg⟩

end

end VG.Proof.Ecdsa.Rfc6979.RISCV64
