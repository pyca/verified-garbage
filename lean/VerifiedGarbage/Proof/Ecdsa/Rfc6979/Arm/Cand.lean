module
-- separate module: its proofs (the candidate loop) build in parallel with `Core`'s, which `Loop` also imports

import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Prep
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: the candidate

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Cand.lean`): the candidate `T`,
at `fT`, its length at `fTlen`: empty (`tInit_ok`), then, while it is
shorter than `Q` bytes, `V = HMAC_K(V)` appended to it (`step_ok`:
`hmacV_ok`, `keepArgs_ok`, `cp_ok`, `tStep_ok`), which the loop does
`nV P = ⌈Q / D⌉` times, RFC 6979's number of blocks (`nV_eq`): `T` is then
`genT`'s (`loop_ok`), and `k`, its first `Q` bytes, shifted right by `sh`
bits if `big` (`candTop_ok`), is `bits2int` of it (`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.AesGcm.Arm (copyLoop imm)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_str op2_reg op2_imm dpVal)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `T`'s length. -/
abbrev tlen {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 32 := m.readW (L.B + BitVec.ofNat 64 488) 32

/-- Where `T` is, and `core` reads `k`. -/
abbrev kArg {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 352

/-- `T`'s first `n` bytes. -/
abbrev tOf {dn : Nat} (L : Lay dn) (m : Mem) (n : Nat) : List Byte := Spec.Sha256.bytesAt m (kArg L) n

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
    (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K k V).1.length = k * P.F.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    rw [genT_succ, List.length_append, genT_length P K k V]
    rw [show (Spec.Hmac.hmac P.ok.hH.SH.H K _).length = P.F.H.D from P.mac_length _ _, Nat.succ_mul]

/-! ## The blocks -/

/-- A word stored to the frame at `o`, through `r0`. -/
theorem strF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho : o + 4 ≤ 468) {v : BitVec 32}
    (h0 : u.gpr .r0 = v) :
    WP isa (.block [.str .r0 .r8 o]) u fun u' => Ctx L g m₀ u' ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 4⟩] u.mem u'.mem ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 (24 + o)) 32 = v := by
  refine wp_strS (a := L.B + BitVec.ofNat 64 (24 + o)) (by omega_arith) (by rw [hc.r8]; exact hL.fpA (by omega_arith))
    (hc.inFrW (by omega_arith) (by omega_arith)) fun u₁ v₁ => WP.block_nil ?_
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 4⟩] u.mem u₁.mem := by
    rw [v₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.keep hL v₁.rd v₁.wr v₁.sp (fun r _ => by rw [v₁.gpr]) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)) v₁.syms,
    v₁.gpr, hf, by rw [v₁.mem, Mem.readW_writeW_self32, h0]⟩

/-- `T` empty. -/
theorem tInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.tInit) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 488, 4⟩] t.mem t'.mem ∧ tlen L t'.mem = BitVec.ofNat 32 0 ∧
      t'.gpr .r9 = t.gpr .r9 := by
  rw [Cfg.tInit]
  refine wp_movS (op2_imm (by decide)) fun u₁ v₁ => ?_
  refine WP.mono (strF_ok hL (hc.upd v₁ (by decide)) (o := fTlen) (by decide) v₁.gpr) fun u ⟨c, g, f, h⟩ => ?_
  rw [show 24 + fTlen = 488 from rfl] at f h
  exact ⟨c, by rw [← v₁.mem]; exact f, h, by rw [g, v₁.other _ (by decide)]⟩

/-- The arguments of `V`'s copy to the end of `T`, of `a` bytes: `V` in
`r1`, `T + a` in `r2`, `r3 = D`. -/
theorem keepArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {a : Nat}
    (ha : tlen L t.mem = BitVec.ofNat 32 a) :
    WP isa (.block Cfg.keepArgs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .r1 = L.fp + BitVec.ofNat 32 fV ∧ u.gpr .r2 = L.fp + BitVec.ofNat 32 (fT + a) ∧
      u.gpr .r3 = BitVec.ofNat 32 P.F.H.D ∧ u.gpr .r9 = t.gpr .r9 := by
  rw [Cfg.keepArgs]
  refine fpAdd_ok hc (d := .r1) (by decide) (o := fV) (by decide) fun u₁ c₁ m₁ v₁ k₁ => ?_
  refine fpAdd_ok c₁ (d := .r2) (by decide) (o := fT) (by decide) fun u₂ c₂ m₂ v₂ k₂ => ?_
  refine frLd_ok hL c₂ (d := .r0) (by decide) (o := fTlen) (by decide) fun u₃ c₃ m₃ v₃ k₃ => ?_
  refine wp_dpS (op2_reg _ _) fun u₄ v₄ => ?_
  have c₄ := c₃.upd v₄ (by decide)
  refine ldD_ok hL c₄ (d := .r3) (by decide) fun u₅ c₅ m₅ v₅ k₅ => WP.block_nil ?_
  refine ⟨c₅, by rw [m₅, v₄.mem, m₃, m₂, m₁], ?_, ?_, by rw [v₅, hT.1], by
    rw [k₅ _ (by decide), v₄.other _ (by decide), k₃ _ (by decide), k₂ _ (by decide), k₁ _ (by decide)]⟩
  · rw [k₅ _ (by decide), v₄.other _ (by decide), k₃ _ (by decide), k₂ _ (by decide), v₁]
  · rw [k₅ _ (by decide), v₄.gpr, dpVal, k₃ _ (by decide), v₂, v₃, m₂, m₁,
      show t.mem.readW (L.B + BitVec.ofNat 64 (24 + fTlen)) 32 = tlen L t.mem from rfl, ha, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]

/-- `T` longer by `D` bytes, and `Z` clear iff it is still shorter than `Q`. -/
theorem tStep_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {a : Nat}
    (ha : tlen L u.mem = BitVec.ofNat 32 a) (hn : a + P.F.H.D < 2 ^ 31) :
    WP isa (.block (cfgOf P).tStep) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 488, 4⟩] u.mem u'.mem ∧
      tlen L u'.mem = BitVec.ofNat 32 (a + P.F.H.D) ∧ isa.eval .ne u' = some (decide (a + P.F.H.D < P.Q)) ∧
      u'.gpr .r9 = u.gpr .r9 := by
  have hQ : P.Q < 256 := by anums
  simp only [Cfg.tStep]
  refine frLd_ok hL hc (d := .r0) (by decide) (o := fTlen) (by decide) fun u₁ c₁ m₁ v₁ k₁ => ?_
  refine ldD_ok hL c₁ (d := .r1) (by decide) fun u₂ c₂ m₂ v₂ k₂ => ?_
  refine wp_dpS (op2_reg _ _) fun u₃ v₃ => ?_
  have c₃ := c₂.upd v₃ (by decide)
  have hax : u₃.gpr .r0 = BitVec.ofNat 32 (a + P.F.H.D) := by
    rw [v₃.gpr, dpVal, k₂ _ (by decide), v₁, v₂, hT.1,
      show u.mem.readW (L.B + BitVec.ofNat 64 (24 + fTlen)) 32 = tlen L u.mem from rfl, ha, BitVec.ofNat_add_ofNat]
  rw [show ([.str .r0 .r8 fTlen, .subs .r12 .r0 (imm (cfgOf P).len), .mov .r7 (imm 0), .adc .r7 .r7 (imm 0),
      .dp .sub .r7 .r7 (imm 1), .cmp .r7 (imm 0)] : List Instr) = [.str .r0 .r8 fTlen] ++
      [.subs .r12 .r0 (imm (cfgOf P).len), .mov .r7 (imm 0), .adc .r7 .r7 (imm 0), .dp .sub .r7 .r7 (imm 1),
        .cmp .r7 (imm 0)] from rfl, WP.block_append_iff]
  refine WP.mono (strF_ok hL c₃ (o := fTlen) (by decide) hax) fun u₄ ⟨c₄, g₄, f₄, w₄⟩ => ?_
  rw [show 24 + fTlen = 488 from rfl] at f₄ w₄
  have e₃ : u₃.mem = u.mem := by rw [v₃.mem, m₂, m₁]
  rw [e₃] at f₄
  refine wp_subsC (op2_imm (encodable_lt (by simp only [cfgOf_len]; omega_arith))) fun u₅ v₅ c₅ => ?_
  refine wp_movC (op2_imm (by decide)) fun u₆ v₆ c₆ => wp_adc (op2_imm (by decide)) fun u₇ v₇ => ?_
  refine wp_dpS (op2_imm (by decide)) fun u₈ v₈ => wp_cmpS (op2_imm (by decide)) fun u₉ v₉ z₉ => WP.block_nil ?_
  have c₈ := (((c₄.upd v₅ (by decide)).upd v₆ (by decide)).upd v₇ (by decide)).upd v₈ (by decide)
  have hm : u₉.mem = u₄.mem := by rw [v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem]
  refine ⟨c₈.flags hL v₉, by rw [hm]; exact f₄, by rw [hm]; exact w₄, ?_, by
    rw [v₉.gpr, v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), g₄,
      v₃.other _ (by decide), k₂ _ (by decide), k₁ _ (by decide)]⟩
  show some (!u₉.z) = _
  have hn' : a + P.F.H.D < 2 ^ 32 := by omega_arith
  rw [z₉, v₈.gpr, dpVal, v₇.gpr, v₆.gpr, c₆, c₅, g₄, hax, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt (by simp only [cfgOf_len]; omega_arith), cfgOf_len]
  by_cases h : P.Q ≤ a + P.F.H.D
  · simp only [h, decide_true, ↓reduceIte, show ¬ a + P.F.H.D < P.Q by omega_arith, decide_false]; decide
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, show a + P.F.H.D < P.Q by omega_arith,
      decide_true]; decide

/-! ## The loop -/

/-- What the candidate's loop changes: `scratch`, the stack below the
frame, `K`, `V`, `T` and its length. -/
abbrev CW {dn : Nat} (L : Lay dn) : List Region :=
  [L.SCR, ⟨L.B, 152⟩, ⟨L.B + BitVec.ofNat 64 352, 140⟩]

/-- After `j` of the candidate's `V`s, from `V₀` with the key `K`. -/
structure CI (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t₀ : State)
    (K V₀ : List Byte) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (CW L) t₀.mem u.mem
  k : kOf P L u.mem = K
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K j V₀).2
  len : tlen L u.mem = BitVec.ofNat 32 (j * P.F.H.D)
  t : tOf L u.mem (j * P.F.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K j V₀).1
  r9 : u.gpr .r9 = t₀.gpr .r9

/-- One more `V`. -/
theorem step_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {j : Nat}
    (hj : (j + 1) * P.F.H.D ≤ 136) {u : State} (hI : CI P L g m₀ t₀ K V₀ j u) :
    WP isa (cfgOf P).candStep u fun u' => CI P L g m₀ t₀ K V₀ (j + 1) u' ∧
      isa.eval .ne u' = some (decide ((j + 1) * P.F.H.D < P.Q)) := by
  have hb := hL.B_fit
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  have : fT = 328 := rfl; have : fV = 64 := rfl; have : fTlen = 464 := rfl
  have hjD : (j + 1) * P.F.H.D = j * P.F.H.D + P.F.H.D := Nat.succ_mul _ _
  refine WP.seq (WP.mono (hmacV_ok hL hT hI.ctx) fun u₁ ⟨hc₁, h9₁, hf₁, hk₁, hv₁⟩ => ?_)
  have hl₁ : tlen L u₁.mem = BitVec.ofNat 32 (j * P.F.H.D) := by
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega_arith)
      · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)
  have ht₁ : tOf L u₁.mem (j * P.F.H.D) = tOf L u.mem (j * P.F.H.D) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega_arith)
      · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by omega_arith)
  refine WP.seq (WP.mono (keepArgs_ok hL hT hc₁ hl₁) fun u₂ ⟨hc₂, hm₂, h1, h2, h3, h9₂⟩ => ?_)
  have hpa : State.addr (L.fp + BitVec.ofNat 32 (fT + j * P.F.H.D)) = L.B + BitVec.ofNat 64 (352 + j * P.F.H.D) := by
    rw [hL.fpA (by omega_arith)]; congr 2; omega_arith
  have hqa : State.addr (L.fp + BitVec.ofNat 32 fV) = L.B + BitVec.ofNat 64 88 := hL.fpA (by omega_arith)
  refine WP.seq (WP.mono (cp_ok hL hc₂ (p := L.fp + BitVec.ofNat 32 (fT + j * P.F.H.D))
      (q := L.fp + BitVec.ofNat 32 fV) (n := P.F.H.D) (by omega_arith) (by omega_arith) h1 h2 h3
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      (by rw [hqa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact safe_low L (by omega_arith))
      (by rw [hpa, hqa]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)))
    fun u₃ ⟨hc₃, g₃, hf₃, hb₃⟩ => ?_)
  rw [hpa, hm₂] at hf₃
  rw [hpa, hqa, hm₂] at hb₃
  have hl₃ : tlen L u₃.mem = BitVec.ofNat 32 (j * P.F.H.D) := by
    rw [← hl₁]
    exact hf₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)
  refine WP.mono (tStep_ok hL hT hc₃ hl₃ (by omega_arith)) fun u₄ ⟨hc₄, hf₄, hl₄, hev₄, h9₄⟩ => ?_
  -- What the copy and the length's store keep.
  have kp : ∀ {o n : Nat}, 24 ≤ o → o + n ≤ 352 →
      Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) n :=
    fun h₁ h₂ => by
      rw [bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith),
        bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith)]
  have hK : kOf P L u₄.mem = K := by
    rw [show kOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 24) P.F.H.D from rfl,
      kp (by decide) (by omega_arith)]
    exact hk₁.trans hI.k
  refine ⟨⟨hc₄, ?_, hK, ?_, ?_, ?_, by
    rw [h9₄, g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), h9₂, h9₁, hI.r9]⟩, by rw [hev₄, hjD]⟩
  · refine ((hI.frame.trans (hf₁.sub fun r hr => ?_)).trans (hf₃.sub fun r hr => ?_)).trans (hf₄.sub fun r hr => ?_)
    · simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨L.B, 152⟩, by simp, sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 352, 140⟩, by simp, Offset.sub _ (by omega_arith) (by omega_arith)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 352, 140⟩, by simp, Offset.sub _ (by omega_arith) (by omega_arith)⟩
  · rw [show vOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 88) P.F.H.D from rfl,
      kp (by decide) (by omega_arith), genT_succ]
    show vOf P L u₁.mem = _
    rw [hv₁, hI.k, hI.v]
  · rw [hl₄, hjD]
  · show Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 352) ((j + 1) * P.F.H.D) = _
    rw [hjD, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith),
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith),
      hb₃, bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith)]
    rw [show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 352) (j * P.F.H.D) = tOf L u₁.mem (j * P.F.H.D)
      from rfl, ht₁, hI.t, genT_succ,
      show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 88) P.F.H.D = vOf P L u₁.mem from rfl, hv₁, hI.k, hI.v]

/-- The number of `V`s in a candidate: `⌈Q / D⌉`. -/
abbrev RfcHash.nV (P : RfcHash) : Nat := (P.Q + P.F.H.D - 1) / P.F.H.D

theorem nV_lt (P : RfcHash) (j : Nat) : j + 1 < P.nV ↔ (j + 1) * P.F.H.D < P.Q := by
  obtain ⟨_, _, _, _, hD16, _, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, hQ8, _, _, _⟩ := P.wsizes
  rw [RfcHash.nV, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega_arith), Nat.succ_mul (j + 1)]
  omega_arith

theorem nV_facts (P : RfcHash) : 1 ≤ P.nV ∧ P.nV * P.F.H.D ≤ P.Q + P.F.H.D - 1 ∧ P.Q ≤ P.nV * P.F.H.D := by
  obtain ⟨_, _, _, _, hD16, _, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, hQ8, _, _, _⟩ := P.wsizes
  have e₁ := Nat.div_mul_le_self (P.Q + P.F.H.D - 1) P.F.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.F.H.D - 1) (show 0 < P.F.H.D by omega_arith)
  have e₃ : 1 ≤ P.nV := (Nat.le_div_iff_mul_le (by omega_arith)).mpr (by omega_arith)
  simp only [RfcHash.nV] at e₃ ⊢
  generalize (P.Q + P.F.H.D - 1) / P.F.H.D = N at e₁ e₂ e₃ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  omega_arith

/-- RFC 6979's number of blocks is `⌈Q / D⌉`. -/
theorem nV_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nV := by
  obtain ⟨_, _, _, _, hD16, _, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, hQ8, _, _, _⟩ := P.wsizes
  have hl := P.R.nBits_len
  have e₁ := Nat.div_mul_le_self (P.Q + P.F.H.D - 1) P.F.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.F.H.D - 1) (show 0 < P.F.H.D by omega_arith)
  rw [Spec.Ecdsa.Rfc6979.blocks]
  simp only [RfcHash.nV, RfcHash.Q] at e₁ e₂ hQ8 ⊢
  generalize (P.R.E.C.len + P.F.H.D - 1) / P.F.H.D = N at e₁ e₂ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  have h₁ : N * (8 * P.F.H.D) = 8 * (N * P.F.H.D) := Nat.mul_left_comm _ _ _
  have h₂ : (N + 1) * (8 * P.F.H.D) = 8 * (N * P.F.H.D) + 8 * P.F.H.D := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  exact Nat.div_eq_of_lt_le (by omega_arith) (by omega_arith)

/-- The loop: `nV` `V`s. -/
theorem loop_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {u : State}
    (hI : CI P L g m₀ t₀ K V₀ 0 u) :
    WP isa (.loop (cfgOf P).candStep .ne) u (CI P L g m₀ t₀ K V₀ P.nV) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨_, _, _, _, _, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, _, hQ66, _, _⟩ := P.wsizes
  refine WP.loop (M := isa) (fun (n : Nat) (s : State) => ∃ j, n = P.nV - j ∧ j < P.nV ∧ CI P L g m₀ t₀ K V₀ j s)
    ?_ (P.nV - 0) u ⟨0, rfl, hN1, hI⟩
  rintro n s ⟨j, rfl, hj, hIj⟩
  have hb : (j + 1) * P.F.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega_arith) (Nat.le_refl P.F.H.D)) (by omega_arith)
  refine WP.mono (step_ok hL hT hb hIj) fun s' ⟨hI', hev⟩ => ?_
  by_cases hlt : j + 1 < P.nV
  · exact .inr ⟨by rw [hev, decide_eq_true ((nV_lt P j).mp hlt)],
      P.nV - (j + 1), by omega_arith, j + 1, rfl, hlt, hI'⟩
  · refine .inl ⟨by rw [hev, decide_eq_false (fun h => hlt ((nV_lt P j).mpr h))], ?_⟩
    rw [show P.nV = j + 1 by omega_arith]; exact hI'

/-! ## The candidate -/

/-- `T` empty: no `V`s yet. -/
theorem tInit_ci (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.tInit) t (CI P L g m₀ t (kOf P L t.mem) (vOf P L t.mem) 0) := by
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  have hb := hL.B_fit
  refine WP.mono (tInit_ok hL hc) fun u₀ ⟨hc₀, hf₀, hl₀, h9₀⟩ => ?_
  have kv0 : ∀ {o : Nat}, 24 ≤ o → o + P.F.H.D ≤ 152 →
      Spec.Sha256.bytesAt u₀.mem (L.B + BitVec.ofNat 64 o) P.F.H.D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 o) P.F.H.D := fun h₁ h₂ =>
    bytesAt_frame hf₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith)
  exact
    { ctx := hc₀
      frame := hf₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨L.B + BitVec.ofNat 64 352, 140⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      k := kv0 (by decide) (by omega_arith)
      v := kv0 (by decide) (by omega_arith)
      len := by rw [hl₀, Nat.zero_mul]
      t := by simp [Spec.Sha256.bytesAt, Spec.Ecdsa.Rfc6979.genT]
      r9 := h9₀ }

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- If `big`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) (hW : P.R.big = true) (hsh : P.R.sh ≠ 0) (hsh8 : P.R.sh < 8) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).candTop) t fun u => Ctx L g m₀ u ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨kArg L, P.Q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (kArg L) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (kArg L) P.Q) >>> P.R.sh) ∧
      u.gpr .r9 = t.gpr .r9 := by
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have hbc : (cfgOf P).big = true := hW
  rw [Cfg.candTop, hbc, ite_eq_left_of_eq_true _ _ (eq_self true), hsc]
  exact WP.mono (conv_ok hL hW hc (o := fT) (s := P.R.sh) (by decide) (by decide) (by decide) (by omega_arith)
    (by omega_arith)) fun u₂ ⟨hc₂, g₂, hf₂, hb₂⟩ =>
      ⟨hc₂, hf₂, hb₂, g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- The candidate: `nV` successive `V = HMAC_K(V)`, and `k`, whose number is
`bits2int` of their concatenation, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ u.gpr .r9 = t.gpr .r9 ∧ Frame (CW L) t.mem u.mem ∧
      kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
          (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 := by
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  have hb := hL.B_fit
  have hl := P.R.nBits_len
  obtain ⟨-, hND, hQN⟩ := nV_facts P
  rw [Cfg.cand]
  refine WP.seq (WP.mono (tInit_ci (P := P) hL hc) fun u₀ hI0 => ?_)
  refine WP.seq (WP.mono (loop_ok hL hT hI0) fun u₁ hI₁ => ?_)
  have hTl := genT_length P (kOf P L t.mem) P.nV (vOf P L t.mem)
  have hbits : Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
      (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (kArg L) P.Q) >>> P.R.sh := by
    rw [Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith)
      (by rw [hTl]; exact hQN),
      show (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
        Spec.Sha256.bytesAt u₁.mem (kArg L) (P.nV * P.F.H.D) from hI₁.t.symm,
      ← bytesAt_take _ _ hQN, show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh by rw [hl.2.2]]
  cases hbg : P.R.big
  · have hsh : P.R.sh = 0 := by have := (P.R.sizesA hbg).2.2.1; omega_arith
    rw [show (cfgOf P).candTop = [] by simp only [Cfg.candTop, show (cfgOf P).big = false from hbg,
      Bool.false_eq_true, ite_false], WP.block_nil_iff]
    exact ⟨hI₁.ctx, hI₁.r9, hI₁.frame, hI₁.k, hI₁.v, by rw [hbits, hsh, Nat.shiftRight_zero]⟩
  · have hsh8 : P.R.sh < 8 := by omega_arith
    have hsh0 : P.R.sh ≠ 0 := by have := (P.R.sizesW hbg); omega_arith
    refine WP.mono (candTop_ok hL hbg hsh0 hsh8 hI₁.ctx) fun u ⟨hcu, hf, hbu, h9u⟩ => ?_
    have kv : ∀ {o : Nat}, 24 ≤ o → o + P.F.H.D ≤ 152 →
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 o) P.F.H.D =
          Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) P.F.H.D := fun h₁ h₂ =>
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by omega_arith) (by decide)
        · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith)
    refine ⟨hcu, h9u.trans hI₁.r9, hI₁.frame.trans (hf.sub fun r hr => ?_), (kv (by decide) (by omega_arith)).trans hI₁.k,
      (kv (by decide) (by omega_arith)).trans hI₁.v, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 352, 140⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    · rw [hbu, hbits, ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
          have := ofBytes_lt (Spec.Sha256.bytesAt u₁.mem (kArg L) P.Q)
          rwa [length_bytesAt] at this))]

end VG.Proof.Ecdsa.Rfc6979.Arm
