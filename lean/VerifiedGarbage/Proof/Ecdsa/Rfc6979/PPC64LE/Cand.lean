module
-- separate module: its proofs (the candidate loop) build in parallel with `Core`'s, which `Loop` also imports

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Prep
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step

/-!
# Deterministic ECDSA on PPC64LE: the candidate

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Cand.lean`): the candidate `T`,
at `fT` above the frame's pointers, its length at `fTlen`: empty
(`tInit_ok`), then, while it is shorter than `Q` bytes, `V = HMAC_K(V)`
appended to it (`step_ok`: `hmacVR_ok`, `keepArgs_ok`, `cp_ok`, `tStep_ok`,
whose `r12` is the borrow of `|T| - Q` as a mask), which the loop does
`nV P = ⌈Q / D⌉` times, RFC 6979's number of blocks (`nV_eq`): `T` is then
`genT`'s (`loop_ok`), and `k`, its first `Q` bytes, shifted right by `sh`
bits if `big` (`candTop_ok`), is `bits2int` of it (`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- `T`'s length. -/
abbrev tlen (L : Lay dn) (m : Mem) : BitVec 64 := m.readW (L.B + BitVec.ofNat 64 (96 + fTlen)) 64

/-- `T`'s first `n` bytes. -/
abbrev tOf (L : Lay dn) (m : Mem) (n : Nat) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (96 + fT)) n

/-- Where `core` reads `k`: `T`. -/
abbrev kArg (_P : RfcHash) (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 (96 + fT)

/-! ## The blocks -/

/-- `T` empty. -/
theorem tInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.tInit) t fun t' => Ctx L g lr m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (96 + fTlen), 8⟩] t.mem t'.mem ∧ tlen L t'.mem = BitVec.ofNat 64 0 := by
  refine WP.of_syms (stepLi (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  refine stepAddSp (by decide) fun t₂ k₂ m₂ v₂ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 (96 + fTlen)) (by decide) (by decide)
    (by rw [v₂, k₁.sp, hc.sp, BitVec.add_zero, fr_add])
    (by rw [k₂.wr, k₁.wr]; exact hc.inFrW (by decide) (by decide)) fun t₃ k₃ g₃ m₃ => wp_nil fun hsy => ?_
  have K : Kp [.r9, .r11] t t₃ := (k₁.mono.trans k₂.mono).trans k₃.mono
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (96 + fTlen), 8⟩] t.mem t₃.mem := by
    rw [m₃, m₂, m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl <;> simp [preserved] at hr)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by decide)) hsy, hf, ?_⟩
  show Mem.readW _ _ 64 = _
  rw [m₃, Mem.readW_writeW_self64, k₂.gpr _ (by decide), v₁]

/-- The arguments of `V`'s copy to the end of `T`, of `a` bytes: `V` in
`r4`, `T + a` in `r5`, `r6 = D`. -/
theorem keepArgs_ok (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) {a : Nat}
    (ha : tlen L t.mem = BitVec.ofNat 64 a) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Kp [.r4, .r5, .r6, .r9, .r11] t u → u.mem = t.mem → u.gpr .r4 = L.B + BitVec.ofNat 64 (96 + fV) →
      u.gpr .r5 = L.B + BitVec.ofNat 64 (96 + fT + a) → u.gpr .r6 = BitVec.ofNat 64 P.v.H.D →
      WP isa (.block is) u Q) :
    WP isa (.block (Cfg.keepArgs ++ is)) t Q := by
  simp only [Cfg.keepArgs, List.cons_append, List.nil_append]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepAddSp (by decide) fun t₂ k₂ m₂ v₂ => ?_
  refine stepAddSp (by decide) fun t₃ k₃ m₃ v₃ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 (96 + fTlen)) (by decide) (by decide)
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb, fr_add])
    (by rw [k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hc.inFr (by decide) (by decide))
    fun t₄ k₄ m₄ v₄ => ?_
  refine stepAdd fun t₅ k₅ m₅ v₅ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide)
    (by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb, fr_add]; rfl)
    (by rw [k₅.rd, k₅.wr, k₄.rd, k₄.wr, k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hc.inFr (by omega) (by omega))
    fun t₆ k₆ m₆ v₆ => ?_
  have hm : t₆.mem = t.mem := by rw [m₆, m₅, m₄, m₃, m₂, m₁]
  refine k t₆ (((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono) hm ?_ ?_ ?_
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, k₁.sp, hc.sp,
      fr_add]
  · rw [k₆.gpr _ (by decide), v₅, k₄.gpr _ (by decide), v₃, v₄, m₃, m₂, m₁,
      show t.mem.readW (L.B + BitVec.ofNat 64 (96 + fTlen)) 64 = tlen L t.mem from rfl, ha, k₂.sp, k₁.sp, hc.sp,
      fr_add, Offset.add_add, Nat.add_assoc]
  · rw [v₆, m₅, m₄, m₃, m₂, m₁, hc.dl hT]

/-- `|T| < Q` from the borrow of `|T| - Q`, as a mask. -/
theorem mask_lt {a q : Nat} (_ha : a < 2 ^ 63) (hq : q < 2 ^ 63) :
    (BitVec.ofNat 64 ((a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64 + (2 ^ 64 - 1 - (a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64) +
      (decide (2 ^ 64 ≤ a + (2 ^ 64 - 1 - q) + 1)).toNat) != 0) = decide (a < q) := by
  by_cases h : q ≤ a
  · rw [decide_eq_true (by omega : 2 ^ 64 ≤ a + (2 ^ 64 - 1 - q) + 1), decide_eq_false (by omega : ¬ a < q),
      show (a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64 + (2 ^ 64 - 1 - (a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64) +
        (true).toNat = 2 ^ 64 by simp only [Bool.toNat_true]; omega]
    rfl
  · rw [decide_eq_false (by omega : ¬ 2 ^ 64 ≤ a + (2 ^ 64 - 1 - q) + 1), decide_eq_true (by omega : a < q),
      show (a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64 + (2 ^ 64 - 1 - (a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64) +
        (false).toNat = 2 ^ 64 - 1 by simp only [Bool.toNat_false]; omega]
    rfl

/-- `T` longer by `D` bytes, and `r12 ≠ 0` iff it is still shorter than `Q`. -/
theorem tStep_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g lr m₀ u) {a : Nat}
    (ha : tlen L u.mem = BitVec.ofNat 64 a) (hn : a + P.v.H.D < 2 ^ 63) :
    WP isa (.block (cfgOf P).tStep) u fun u' => Ctx L g lr m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (96 + fTlen), 8⟩] u.mem u'.mem ∧
      tlen L u'.mem = BitVec.ofNat 64 (a + P.v.H.D) ∧
      isa.eval (.nonzero .d .r12) u' = some (decide (a + P.v.H.D < P.Q)) := by
  have hs := P.sizes
  simp only [Cfg.tStep]
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 (96 + fTlen)) (by decide) (by decide) (by rw [hb, fr_add])
    (hc.inFrK k₁ (by decide) (by decide)) fun t₂ k₂ m₂ v₂ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide)
    (by rw [k₂.gpr _ (by decide), hb, fr_add]; rfl)
    (by rw [k₂.rd, k₂.wr]; exact hc.inFrK k₁ (by omega) (by omega)) fun t₃ k₃ m₃ v₃ => ?_
  refine stepAdd fun t₄ k₄ m₄ v₄ => ?_
  have e9 : t₄.gpr .r9 = BitVec.ofNat 64 (a + P.v.H.D) := by
    rw [v₄, k₃.gpr _ (by decide), v₂, v₃, m₂, m₁, show u.mem.readW (L.B + BitVec.ofNat 64 (96 + fTlen)) 64 =
      tlen L u.mem from rfl, ha, hc.dl hT, BitVec.ofNat_add_ofNat]
  refine stepStd (a := L.B + BitVec.ofNat 64 (96 + fTlen)) (by decide) (by decide)
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb, fr_add])
    (by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr]; exact hc.inFrW (by decide) (by decide)) fun t₅ k₅ g₅ m₅ => ?_
  refine stepLi (show (cfgOf P).len < 2 ^ 15 by show P.Q < _; omega) fun t₆ k₆ m₆ v₆ => ?_
  refine stepSubc fun t₇ k₇ m₇ v₇ c₇ => ?_
  refine stepSube fun t₈ k₈ m₈ v₈ => wp_nil fun hsy => ?_
  have K : Kp [.r9, .r10, .r11, .r12] u t₈ :=
    ((((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono).trans k₇.mono).trans
      k₈.mono
  have hm : t₈.mem = t₄.mem.writeW (L.B + BitVec.ofNat 64 (96 + fTlen)) (t₄.gpr .r9) := by
    rw [m₈, m₇, m₆, m₅]
  have hm₄ : t₄.mem = u.mem := by rw [m₄, m₃, m₂, m₁]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (96 + fTlen), 8⟩] u.mem t₈.mem := by
    rw [hm, hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl | rfl | rfl <;> simp [preserved] at hr)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by decide)) hsy, hf,
    by show Mem.readW _ _ 64 = _; rw [hm, Mem.readW_writeW_self64, e9], ?_⟩
  have e9' : (t₆.gpr .r9).toNat = a + P.v.H.D := by
    rw [k₆.gpr _ (by decide), g₅, e9, BitVec.toNat_ofNat]; omega
  have e10 : (t₆.gpr .r10).toNat = P.Q := by rw [v₆, BitVec.toNat_ofNat]; show P.Q % _ = _; omega
  refine (eval_nonzero t₈ .r12).trans ?_
  rw [v₈, v₇, c₇, e9', e10, BitVec.toNat_ofNat]
  exact congrArg some (mask_lt (a := a + P.v.H.D) (q := P.Q) (by omega) (by omega))

/-! ## The loop -/

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

theorem genT_length (P : RfcHash) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    (Spec.Ecdsa.Rfc6979.genT P.v.l.ok.SH.H K k V).1.length = k * P.v.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    rw [genT_succ, List.length_append, genT_length P K k V, mac_length]
    rw [Nat.succ_mul]

/-- What the candidate's loop changes: `scratch`, the stack below the
frame's pointers, and `T`. -/
abbrev CW (L : Lay dn) : List Region :=
  [L.SCR, ⟨L.B, 264⟩, ⟨L.B + BitVec.ofNat 64 (96 + fT), 136⟩]

/-- After `j` of the candidate's `V`s, from `V₀` with the key `K`. -/
structure CI (P : RfcHash) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t₀ : State)
    (K V₀ : List Byte) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  frame : Frame (CW L) t₀.mem u.mem
  k : kOf P L u.mem = K
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.v.l.ok.SH.H K j V₀).2
  len : tlen L u.mem = BitVec.ofNat 64 (j * P.v.H.D)
  t : tOf L u.mem (j * P.v.H.D) = (Spec.Ecdsa.Rfc6979.genT P.v.l.ok.SH.H K j V₀).1
  saved : SavedK P L u.mem K

/-- One more `V`. -/
theorem step_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {j : Nat}
    (hj : (j + 1) * P.v.H.D ≤ 136) {u : State} (hI : CI P L g lr m₀ t₀ K V₀ j u) :
    WP isa (cfgOf P).candStep u fun u' => CI P L g lr m₀ t₀ K V₀ (j + 1) u' ∧
      isa.eval (.nonzero .d .r12) u' = some (decide ((j + 1) * P.v.H.D < P.Q)) := by
  have hnB := hL.nB
  have hs := P.sizes
  have hjD : (j + 1) * P.v.H.D = j * P.v.H.D + P.v.H.D := Nat.succ_mul _ _
  have hS : SavedK P L u.mem (kOf P L u.mem) := by rw [hI.k]; exact hI.saved
  have hkl := blockKey_length (P := P) (keyOf_length (L := L) u.mem)
  refine WP.seq (WP.mono (hmacVR_ok hL hT hI.ctx hS) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hS₁⟩ => ?_)
  have hl₁ : tlen L u₁.mem = BitVec.ofNat 64 (j * P.v.H.D) := by
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fTlen]; omega)
      · exact Offset.disjoint_base _ (by simp only [fTlen]; omega) (by simp only [fTlen]; omega)) (by decide)
  have ht₁ : Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (96 + fT)) (j * P.v.H.D) =
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fT)) (j * P.v.H.D) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fT]; omega)
      · exact Offset.disjoint_base _ (by simp only [fT]; omega) (by simp only [fT]; omega)) (by omega)
  refine WP.seq (WP.of_syms ?_)
  rw [← List.append_nil Cfg.keepArgs]
  refine keepArgs_ok (is := []) hT hc₁ hl₁ fun u₂ k₂ m₂ h4 h5 h6 => wp_nil fun hsy₂ => ?_
  have hc₂ : Ctx L g lr m₀ u₂ := hc₁.kp hL k₂ m₂ hsy₂
  refine WP.seq (WP.mono (cp_ok hL hc₂ (p := L.B + BitVec.ofNat 64 (96 + fT + j * P.v.H.D))
      (q := L.B + BitVec.ofNat 64 (96 + fV)) (n := P.v.H.D) (by omega) (by omega) h4 h5 h6
      (fun i hi => by rw [Offset.add_add]; exact hc₂.inFrW (n := 1) (by simp only [fT]; omega) (by simp only [fT]; omega))
      (safe_high L (by simp only [fT]; omega) (by simp only [fT]; omega))
      (fun i hi => by rw [Offset.add_add]; exact hc₂.inFr (n := 1) (by simp only [fV]; omega) (by simp only [fV]; omega))
      (Offset.disjoint _ (.inl (by simp only [fV, fT]; omega)) (by simp only [fV]; omega) (by simp only [fT]; omega))
      (by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by simp only [fT]; omega),
          Nat.mod_eq_of_lt (by simp only [fT]; omega)]; simp only [fT]; omega))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_)
  rw [m₂] at hf₃ hb₃
  have hl₃ : tlen L u₃.mem = BitVec.ofNat 64 (j * P.v.H.D) := by
    rw [← hl₁]
    exact hf₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [fTlen, fT]; omega)) (by simp only [fTlen]; omega)
        (by simp only [fT]; omega)) (by decide)
  refine WP.mono (tStep_ok hL hT hc₃ hl₃ (by omega)) fun u₄ ⟨hc₄, hf₄, hl₄, hcf₄⟩ => ?_
  -- What the copy and the length's store keep.
  have kp : ∀ {o n : Nat}, 96 ≤ o → o + n ≤ 96 + fTlen →
      Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) n :=
    fun h₁ h₂ => by
      rw [bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl h₂) (by simp only [fTlen] at h₂ ⊢; omega) (by simp only [fTlen]; omega))
        (by simp only [fTlen] at h₂; omega),
        bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by simp only [fTlen, fT] at h₂ ⊢; omega)) (by simp only [fTlen] at h₂ ⊢; omega)
            (by simp only [fT]; omega)) (by simp only [fTlen] at h₂; omega)]
  have hK : kOf P L u₄.mem = K := by
    rw [show kOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 128) P.v.H.D from rfl,
      kp (by decide) (by simp only [fTlen]; omega)]
    exact hk₁.trans hI.k
  refine ⟨⟨hc₄, ?_, hK, ?_, ?_, ?_, ?_⟩, by rw [hcf₄, hjD]⟩
  · refine ((hI.frame.trans (hf₁.sub fun r hr => ?_)).trans (hf₃.sub fun r hr => ?_)).trans (hf₄.sub fun r hr => ?_)
    · simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨L.B, 264⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 (96 + fT), 136⟩, by simp, Offset.sub _ (by omega) (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 264⟩, by simp, Offset.sub_base _ (by simp only [fTlen]; omega)⟩
  · rw [show vOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 192) P.v.H.D from rfl,
      kp (by decide) (by simp only [fTlen]; omega), genT_succ]
    show vOf P L u₁.mem = _
    rw [hv₁, hI.k, hI.v]
  · rw [hl₄, hjD]
  · show Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (96 + fT)) ((j + 1) * P.v.H.D) = _
    rw [hjD, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by simp only [fTlen, fT]; omega)) (by simp only [fT]; omega)
          (by simp only [fTlen]; omega)) (by omega),
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by simp only [fTlen, fT]; omega)) (by simp only [fT]; omega)
          (by simp only [fTlen]; omega)) (by omega),
      hb₃, bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega)) (by simp only [fT]; omega) (by simp only [fT]; omega)) (by omega),
      ht₁, show Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fT)) (j * P.v.H.D) = _ from hI.t, genT_succ]
    rw [show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (96 + fV)) P.v.H.D = vOf P L u₁.mem from rfl, hv₁,
      hI.k, hI.v]
  · rw [hk₁, hI.k] at hS₁
    refine (hS₁.frame (by rw [← hI.k]; exact hkl) hf₃ fun r hr => ?_).frame (by rw [← hI.k]; exact hkl)
      hf₄ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (by simp only [fT]; omega) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (by simp only [fTlen]; omega) (by decide)).symm

/-- The number of `V`s in a candidate: `⌈Q / D⌉`. -/
abbrev RfcHash.nV (P : RfcHash) : Nat := (P.Q + P.v.H.D - 1) / P.v.H.D

theorem nV_lt (P : RfcHash) (j : Nat) : j + 1 < P.nV ↔ (j + 1) * P.v.H.D < P.Q := by
  have hs := P.sizes
  rw [RfcHash.nV, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), Nat.succ_mul (j + 1)]
  omega

theorem nV_facts (P : RfcHash) : 1 ≤ P.nV ∧ P.nV * P.v.H.D ≤ P.Q + P.v.H.D - 1 ∧ P.Q ≤ P.nV * P.v.H.D := by
  have hs := P.sizes
  have e₁ := Nat.div_mul_le_self (P.Q + P.v.H.D - 1) P.v.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.v.H.D - 1) (show 0 < P.v.H.D by omega)
  have e₃ : 1 ≤ P.nV := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  simp only [RfcHash.nV] at e₃ ⊢
  generalize (P.Q + P.v.H.D - 1) / P.v.H.D = N at e₁ e₂ e₃ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  omega

/-- `nBits` is within the scalars' last byte. -/
theorem nBits_len (P : RfcHash) : 8 * P.Q < Spec.Ecdsa.nBits P.R.C.E.curve + 8 ∧
    Spec.Ecdsa.nBits P.R.C.E.curve ≤ 8 * P.Q := by
  cases h : P.R.big
  · have := (P.R.sizesA h).2.2.1; simp only [RfcHash.Q, RfcCurve.Q] at this ⊢; omega
  · have := P.R.sizesW h; simp only [RfcHash.Q, RfcCurve.Q] at this ⊢; omega

/-- RFC 6979's number of blocks is `⌈Q / D⌉`. -/
theorem nV_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.C.E.curve P.v.H.D = P.nV := by
  have hs := P.sizes
  have hl := nBits_len P
  have e₁ := Nat.div_mul_le_self (P.Q + P.v.H.D - 1) P.v.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.v.H.D - 1) (show 0 < P.v.H.D by omega)
  rw [Spec.Ecdsa.Rfc6979.blocks]
  simp only [RfcHash.nV] at e₁ e₂ ⊢
  generalize (P.Q + P.v.H.D - 1) / P.v.H.D = N at e₁ e₂ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  have h₁ : N * (8 * P.v.H.D) = 8 * (N * P.v.H.D) := Nat.mul_left_comm _ _ _
  have h₂ : (N + 1) * (8 * P.v.H.D) = 8 * (N * P.v.H.D) + 8 * P.v.H.D := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The loop: `nV` `V`s. -/
theorem loop_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {u : State}
    (hI : CI P L g lr m₀ t₀ K V₀ 0 u) :
    WP isa (.loop (cfgOf P).candStep (.nonzero .d .r12)) u (CI P L g lr m₀ t₀ K V₀ P.nV) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  have hs := P.sizes
  refine WP.loop (M := isa) (fun (n : Nat) (s : State) => ∃ j, n = P.nV - j ∧ j < P.nV ∧ CI P L g lr m₀ t₀ K V₀ j s)
    ?_ (P.nV - 0) u ⟨0, rfl, hN1, hI⟩
  rintro n s ⟨j, rfl, hj, hIj⟩
  have hb : (j + 1) * P.v.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega) (Nat.le_refl P.v.H.D)) (by omega)
  refine WP.mono (step_ok hL hT hb hIj) fun s' ⟨hI', hcf⟩ => ?_
  by_cases hlt : j + 1 < P.nV
  · exact .inr ⟨by rw [hcf, decide_eq_true ((nV_lt P j).mp hlt)], P.nV - (j + 1), by omega, j + 1, rfl, hlt, hI'⟩
  · refine .inl ⟨by rw [hcf, decide_eq_false (fun h => hlt ((nV_lt P j).mpr h))], ?_⟩
    rw [show P.nV = j + 1 by omega]; exact hI'

/-! ## The candidate -/

/-- `T` empty: no `V`s yet. -/
theorem tInit_ci (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.block Cfg.tInit) t (CI P L g lr m₀ t (kOf P L t.mem) (vOf P L t.mem) 0) := by
  have hs := P.sizes
  refine WP.mono (tInit_ok hL hc) fun u₀ ⟨hc₀, hf₀, hl₀⟩ => ?_
  have kv0 : ∀ {o : Nat}, 96 ≤ o → o + P.v.H.D ≤ 256 →
      Spec.Sha256.bytesAt u₀.mem (L.B + BitVec.ofNat 64 o) P.v.H.D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 o) P.v.H.D := fun h₁ h₂ =>
    bytesAt_frame hf₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [fTlen]; omega)) (by omega) (by simp only [fTlen]; omega))
      (by omega)
  exact
    { ctx := hc₀
      frame := hf₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨L.B, 264⟩, by simp, Offset.sub_base _ (by decide)⟩
      k := kv0 (by decide) (by omega)
      v := kv0 (by decide) (by omega)
      len := by rw [hl₀, Nat.zero_mul]
      t := by simp [Spec.Sha256.bytesAt, Spec.Ecdsa.Rfc6979.genT]
      saved := hS.frame (blockKey_length (keyOf_length _)) hf₀ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.stk_scr (by simp only [fTlen]; omega) (by decide)).symm }

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- If `big`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) (hW : P.R.big = true) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block (cfgOf P).candTop) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + fT), 66⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fT)) 66 =
        Spec.Weierstrass.toBytes 66
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (96 + fT)) 66) >>> P.R.sh) := by
  obtain ⟨hw9, hQ66, -⟩ := P.sizesW hW
  have hsh := P.R.sh7 hW
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have hbc : (cfgOf P).big = true := hW
  rw [Cfg.candTop, hbc, ite_eq_left_of_eq_true _ _ (eq_self true), hsc]
  exact WP.mono (conv_ok hL (c := cfgOf P) (o := fT) (s := P.R.sh) hQ66 hw9 hc (by decide) (by decide) (by omega)
    (by omega)) fun u ⟨hcu, _, hf, hb⟩ => ⟨hcu, hf, hb⟩

/-- The candidate: `nV` successive `V = HMAC_K(V)`, and `k`, whose number is
`bits2int` of their concatenation, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).cand t fun u => Ctx L g lr m₀ u ∧ Frame (CW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.v.l.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg P L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.C.E.curve
          (Spec.Ecdsa.Rfc6979.genT P.v.l.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 ∧
      SavedK P L u.mem (kOf P L t.mem) := by
  have hs := P.sizes
  have hl := nBits_len P
  obtain ⟨-, hND, hQN⟩ := nV_facts P
  rw [Cfg.cand]
  refine WP.seq (WP.mono (tInit_ci hL hc hS) fun u₀ hI0 => ?_)
  refine WP.seq (WP.mono (loop_ok hL hT hI0) fun u₁ hI₁ => ?_)
  have hTl := genT_length P (kOf P L t.mem) P.nV (vOf P L t.mem)
  have hsh : 8 * P.Q - Spec.Ecdsa.nBits P.R.C.E.curve = P.R.sh := by rw [P.R.sh_eq]
  have hbits : Spec.Ecdsa.Rfc6979.bits2int P.R.C.E.curve
      (Spec.Ecdsa.Rfc6979.genT P.v.l.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (kArg P L) P.Q) >>> P.R.sh := by
    rw [Spec.Ecdsa.Rfc6979.bits2int, Rfc6979.hashToInt_takeR (R := P.Q) hl.2 (by rw [hTl]; exact hQN),
      show (Spec.Ecdsa.Rfc6979.genT P.v.l.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
        Spec.Sha256.bytesAt u₁.mem (kArg P L) (P.nV * P.v.H.D) from hI₁.t.symm,
      bytesAt_take _ _ hQN, hsh]
  cases hb : P.R.big
  · have hsh0 : P.R.sh = 0 := P.R.sh0 hb
    rw [show (cfgOf P).candTop = [] by simp only [Cfg.candTop, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false], WP.block_nil_iff]
    exact ⟨hI₁.ctx, hI₁.frame, hI₁.k, hI₁.v, by rw [hbits, hsh0, Nat.shiftRight_zero], hI₁.saved⟩
  · have hQ66 : P.Q = 66 := (P.sizesW hb).2.1
    refine WP.mono (candTop_ok hL hb hI₁.ctx) fun u ⟨hcu, hf, hbu⟩ => ?_
    have kv : ∀ {o : Nat}, 96 ≤ o → o + P.v.H.D ≤ 256 →
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 o) P.v.H.D =
          Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) P.v.H.D := fun h₁ h₂ =>
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by omega) (by decide)
        · exact Offset.disjoint _ (.inl (by simp only [fT]; omega)) (by omega) (by simp only [fT]; omega)) (by omega)
    refine ⟨hcu, hI₁.frame.trans (hf.sub fun r hr => ?_), (kv (by decide) (by omega)).trans hI₁.k,
      (kv (by decide) (by omega)).trans hI₁.v, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 (96 + fT), 136⟩, by simp, Region.sub_prefix (by omega)⟩
    · rw [show kArg P L = L.B + BitVec.ofNat 64 (96 + fT) from rfl, hQ66, hbu, hbits, hQ66,
        Rfc6979.ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
          have := Rfc6979.ofBytes_lt (Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (96 + fT)) 66)
          rwa [length_bytesAt] at this))]
    · refine hI₁.saved.frame (blockKey_length (keyOf_length (L := L) t.mem)) hf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
      · exact (hL.stk_scr (by simp only [fT]; omega) (by decide)).symm

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
