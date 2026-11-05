module
-- separate module: its proofs (the candidate loop) build in parallel with `Core`'s, which `Loop` also imports

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Prep
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Steps
import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on AArch64: the candidate

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Cand.lean`): the candidate `T`, at
`fT` above the frame's pointers, its length at `fTlen`: empty (`tInit_ok`),
then, while it is shorter than `Q` bytes, `V = HMAC_K(V)` appended to it
(`step_ok`: `hmacVR_ok`, `keepArgs_ok`, `cp_ok`, `tStep_ok`), which the loop
does `nV P = ⌈Q / D⌉` times, RFC 6979's number of blocks (`nV_eq`): `T` is
then `genT`'s (`loop_ok`), and `k`, its first `Q` bytes, shifted right by
`sh` bits if `big` (`candTop_ok`), is `bits2int` of it (`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.RsaOaep.AArch64 (count_loop sbc_self eval_nonzero)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `T`'s length. -/
abbrev tlen {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : BitVec 64 :=
  m.readW (L.B + BitVec.ofNat 64 (16 + fTlen)) 64

/-- `T`'s first `n` bytes. -/
abbrev tOf {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) (n : Nat) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (16 + fT)) n

/-- Where `core` reads the candidate `k`: `T`. -/
abbrev kArg (_P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Addr :=
  L.B + BitVec.ofNat 64 (16 + fT)

/-! ## The blocks -/

/-- A word of `x9` stored at `sp + o`, through `x15`. -/
theorem stF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    {o : Nat} (ho : o % 8 = 0) (ho₂ : 16 + o + 8 ≤ 200) :
    WP isa (.block [.str .x .x9 .x15 o]) u fun u' => Ctx L g m₀ u' ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 8⟩] u.mem u'.mem ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 (16 + o)) 64 = u.gpr .x9 := by
  refine WP.mono_syms (strW_ok (t := .x9) (dst := .x15) (D := L.B + BitVec.ofNat 64 16) (d := o) h15
    ⟨ho, by omega⟩ (by rw [Offset.add_add]; exact hc.inFrW (by omega) (by have := L.he; omega)))
    fun u₂ ⟨hrd, hwr, hsp, hg, _, hm⟩ hsy => ?_
  rw [Offset.add_add] at hm
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 8⟩] u.mem u₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.keep hL hrd hwr hsp (fun r _ _ => by rw [hg]) hf (hsy := hsy)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact safe_low L (by omega)), hg, hf,
    by rw [hm, Mem.readW_writeW_self64]⟩

/-- `T` empty. -/
theorem tInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.tInit) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + fTlen), 8⟩] t.mem t'.mem ∧ tlen L t'.mem = BitVec.ofNat 64 0 := by
  rw [show Cfg.tInit = [.movz .x .x9 0 0] ++ Cfg.fr .x15 0 ++ [.str .x .x9 .x15 fTlen] from rfl,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (movz_ok hL hc (d := .x9) (by decide) (n := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .x15) (by decide) (o := 0) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (stF_ok hL h₂.ctx (by rw [h₂.val]) (o := fTlen) (by decide) (by decide))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  rw [h₂.mem, h₁.mem] at hf₃
  exact ⟨hc₃, hf₃, by show u₃.mem.readW _ 64 = _; rw [hb₃, h₂.keep _ (by decide), h₁.val]⟩

/-- The arguments of `V`'s copy to the end of `T`, of `a` bytes: `V` in
`x11`, `T + a` in `x12` and `x13 = D`. -/
theorem keepArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {a : Nat}
    (ha : tlen L t.mem = BitVec.ofNat 64 a) :
    WP isa (.block Cfg.keepArgs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .x11 = L.B + BitVec.ofNat 64 (16 + fV) ∧ u.gpr .x12 = L.B + BitVec.ofNat 64 (16 + fT + a) ∧
      u.gpr .x13 = BitVec.ofNat 64 P.H.D := by
  have he := L.he
  rw [show Cfg.keepArgs = Cfg.fr .x11 fV ++ Cfg.fr .x12 fT ++ [.ldrSp .x9 fTlen] ++ [.add .x .x12 .x12 .x9] ++
      [.ldrSp .x13 fDl] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x11) (by decide) (o := fV) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .x12) (by decide) (o := fT) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (ldF_ok hL h₂.ctx (d := .x9) (by decide) (o := fTlen) (by simp only [fTlen]; omega) rfl)
    fun u₃ h₃ => ?_
  refine WP.mono (add_ok hL h₃.ctx (d := .x12) (r := .x9) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (ldD_ok hL hT h₄.ctx (d := .x13) (by decide)) fun u₅ h₅ => ?_
  have hm₄ : u₄.mem = t.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨h₅.ctx, by rw [h₅.mem, hm₄], ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.val, h₃.keep _ (by decide), h₂.val, h₃.val, h₂.mem, h₁.mem,
      show t.mem.readW (L.B + BitVec.ofNat 64 (16 + fTlen)) 64 = tlen L t.mem from rfl, ha, Offset.add_add]

/-- `T` longer by `D` bytes, and `x12` nonzero iff it is still shorter than `Q`. -/
theorem tStep_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {a : Nat}
    (ha : tlen L u.mem = BitVec.ofNat 64 a) (hn : a + P.H.D < 2 ^ 63) :
    WP isa (.block (cfgOf P).tStep) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + fTlen), 8⟩] u.mem u'.mem ∧
      tlen L u'.mem = BitVec.ofNat 64 (a + P.H.D) ∧ (u'.gpr .x12 != 0) = decide (a + P.H.D < P.Q) := by
  have he := L.he
  have hQ : P.Q < 2 ^ 16 := by anums
  rw [show (cfgOf P).tStep = [.ldrSp .x9 fTlen] ++ [.ldrSp .x10 fDl] ++ [.add .x .x9 .x9 .x10] ++ Cfg.fr .x15 0 ++
      [.str .x .x9 .x15 fTlen] ++ [.movz .x .x10 (BitVec.ofNat 16 P.Q) 0] ++
      [.subs .x .x12 .x9 .x10, .sbc .x .x12 .x12 .x12] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc (d := .x9) (by decide) (o := fTlen) (by simp only [fTlen]; omega) rfl)
    fun u₁ h₁ => ?_
  refine WP.mono (ldD_ok hL hT h₁.ctx (d := .x10) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (add_ok hL h₂.ctx (d := .x9) (r := .x10) (by decide)) fun u₃ h₃ => ?_
  have h9₃ : u₃.gpr .x9 = BitVec.ofNat 64 (a + P.H.D) := by
    rw [h₃.val, h₂.keep _ (by decide), h₁.val, h₂.val,
      show u.mem.readW (L.B + BitVec.ofNat 64 (16 + fTlen)) 64 = tlen L u.mem from rfl, ha, BitVec.ofNat_add_ofNat]
  refine WP.mono (fr_ok hL h₃.ctx (d := .x15) (by decide) (o := 0) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (stF_ok hL h₄.ctx (by rw [h₄.val]) (o := fTlen) (by decide) (by decide))
    fun u₅ ⟨hc₅, hg₅, hf₅, hb₅⟩ => ?_
  refine WP.mono (movz_ok hL hc₅ (d := .x10) (by decide) (n := P.Q) hQ) fun u₆ h₆ => ?_
  have h9₆ : u₆.gpr .x9 = BitVec.ofNat 64 (a + P.H.D) := by
    rw [h₆.keep _ (by decide), hg₅, h₄.keep _ (by decide), h9₃]
  have hQt : (u₆.gpr .x10).toNat = P.Q := by rw [h₆.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnt : (u₆.gpr .x9).toNat = a + P.H.D := by rw [h9₆, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (show WP isa (.block [.subs .x .x12 .x9 .x10, .sbc .x .x12 .x12 .x12]) u₆ fun u₇ =>
      u₇.rd = u₆.rd ∧ u₇.wr = u₆.wr ∧ u₇.sp = u₆.sp ∧ u₇.mem = u₆.mem ∧ u₇.syms = u₆.syms ∧
      (∀ r, r ≠ .x12 → u₇.gpr r = u₆.gpr r) ∧
      u₇.gpr .x12 = if P.Q ≤ a + P.H.D then 0 else BitVec.allOnes 64 by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
      RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.mem_addWithCarry, RegUpd.gpr_write, RegUpd.mem_write,
      ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨by atriv, by atriv, by atriv, by atriv, by atriv, fun r hr => by simp only [hr, ite_false], ?_⟩
    rw [sbc_self, hQt, hnt]) fun u₇ ⟨hrd₇, hwr₇, hsp₇, hm₇, hsy₇, hg₇, h12₇⟩ => ?_
  have hc₇ : Ctx L g m₀ u₇ := h₆.ctx.regs hL hrd₇ hwr₇ hm₇ hsp₇
    (fun r hr _ => hg₇ r (ne_cs hr (by decide))) hsy₇
  refine ⟨hc₇, by rw [hm₇, h₆.mem]; rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem] at hf₅; exact hf₅,
    by rw [show tlen L u₇.mem = u₇.mem.readW (L.B + BitVec.ofNat 64 (16 + fTlen)) 64 from rfl, hm₇, h₆.mem, hb₅,
      h₄.keep _ (by decide), h9₃], ?_⟩
  rw [h12₇]
  by_cases h : P.Q ≤ a + P.H.D
  · simp only [h, ite_true, show ¬ a + P.H.D < P.Q by omega, decide_false]; rfl
  · simp only [h, ite_false, show a + P.H.D < P.Q by omega, decide_true]; rfl

/-! ## The loop -/

/-- What the candidate's loop changes: `scratch`, the stack below the
frame, `K`, `V` and `T`'s length, and `T`. -/
abbrev CW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region :=
  [L.SCR, ⟨L.B, 152⟩, ⟨L.B + BitVec.ofNat 64 (16 + fT), 136⟩]

/-- After `j` of the candidate's `V`s, from `V₀` with the key `K`. -/
structure CI (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64) (m₀ : Mem) (t₀ : State)
    (K V₀ : List Byte) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (CW L) t₀.mem u.mem
  k : kOf P L u.mem = K
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K j V₀).2
  len : tlen L u.mem = BitVec.ofNat 64 (j * P.H.D)
  t : tOf L u.mem (j * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K j V₀).1
  saved : SavedK P L u.mem K

/-- One more `V`. -/
theorem step_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {j : Nat} (hj : (j + 1) * P.H.D ≤ 136)
    {u : State} (hI : CI P L g m₀ t₀ K V₀ j u) :
    WP isa (cfgOf P).candStep u fun u' => CI P L g m₀ t₀ K V₀ (j + 1) u' ∧
      (u'.gpr .x12 != 0) = decide ((j + 1) * P.H.D < P.Q) := by
  have he := L.he
  have hnb := hL.nB
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hjD : (j + 1) * P.H.D = j * P.H.D + P.H.D := Nat.succ_mul _ _
  have hS : SavedK P L u.mem (kOf P L u.mem) := by rw [hI.k]; exact hI.saved
  refine WP.seq (WP.mono (hmacVR_ok hL hT hI.ctx hS) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hS₁⟩ => ?_)
  have hl₁ : tlen L u₁.mem = BitVec.ofNat 64 (j * P.H.D) := by
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fTlen]; omega)
      · exact Offset.disjoint_base _ (by simp only [fTlen]; omega) (by simp only [fTlen]; omega)) (by decide)
  have ht₁ : Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (16 + fT)) (j * P.H.D) =
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fT)) (j * P.H.D) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fT]; omega)
      · exact Offset.disjoint_base _ (by simp only [fT]; omega) (by simp only [fT]; omega)) (by omega)
  refine WP.seq (WP.mono (keepArgs_ok hL hT hc₁ hl₁) fun u₂ ⟨hc₂, hm₂, hsi₂, hdi₂, hcx₂⟩ => ?_)
  refine WP.seq (WP.mono (cp_ok hL hc₂ (p := L.B + BitVec.ofNat 64 (16 + fT + j * P.H.D))
      (q := L.B + BitVec.ofNat 64 (16 + fV)) (n := P.H.D) (by omega) (by omega) hcx₂ hdi₂ hsi₂ ?_
      (hc₂.inFrW (by omega) (by simp only [fT]; omega))
      (safe_high L (by simp only [fT]; omega) (by simp only [fT]; omega))
      (fun i hi => by
        obtain ⟨R, hR, h⟩ := hc₂.inFrW (d := 16 + fV + i) (n := 1) (by omega) (by simp only [fV]; omega)
        exact ⟨R, List.mem_append_right _ hR, by rw [Offset.add_add]; exact h⟩)
      (fun i hi h => Offset.disjoint L.B (d := 16 + fV + i) (n := 1) (e := 16 + fT + j * P.H.D) (k := P.H.D)
        (.inl (by simp only [fV, fT]; omega)) (by simp only [fV]; omega) (by simp only [fT]; omega) _
        (by rw [← Offset.add_add]; exact Region.contains_self _ _) h))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_)
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + fT + _) (by simp only [fT]; omega),
      Nat.mod_eq_of_lt (by simp only [fT]; omega)]
    simp only [fT]; omega
  rw [hm₂] at hf₃ hb₃
  have hl₃ : tlen L u₃.mem = BitVec.ofNat 64 (j * P.H.D) := by
    rw [← hl₁]
    exact hf₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [fTlen, fT]; omega)) (by simp only [fTlen]; omega)
        (by simp only [fT]; omega)) (by decide)
  refine WP.mono (tStep_ok hL hT hc₃ hl₃ (by omega)) fun u₄ ⟨hc₄, hf₄, hl₄, hcf₄⟩ => ?_
  -- What the copy and the length's store keep.
  have kp : ∀ {o n : Nat}, 16 ≤ o → o + n ≤ 16 + fTlen →
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
    rw [show kOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 16) P.H.D from rfl,
      kp (by decide) (by simp only [fTlen]; omega)]
    exact hk₁.trans hI.k
  refine ⟨⟨hc₄, ?_, hK, ?_, ?_, ?_, ?_⟩, by rw [hcf₄, hjD]⟩
  · refine ((hI.frame.trans (hf₁.sub fun r hr => ?_)).trans (hf₃.sub fun r hr => ?_)).trans (hf₄.sub fun r hr => ?_)
    · simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨L.B, 152⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 (16 + fT), 136⟩, by simp, Offset.sub _ (by omega) (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 152⟩, by simp, Offset.sub_base _ (by simp only [fTlen]; omega)⟩
  · rw [show vOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 80) P.H.D from rfl,
      kp (by decide) (by simp only [fTlen]; omega), genT_succ]
    show vOf P L u₁.mem = _
    rw [hv₁, hI.k, hI.v]
  · rw [hl₄, hjD]
  · show Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (16 + fT)) ((j + 1) * P.H.D) = _
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
      ht₁, show Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fT)) (j * P.H.D) = _ from hI.t, genT_succ]
    rw [show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (16 + fV)) P.H.D = vOf P L u₁.mem from rfl, hv₁, hI.k,
      hI.v]
  · rw [hk₁, hI.k] at hS₁
    refine (hS₁.frame hf₃ fun r hr => ?_).frame hf₄ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (by simp only [fT]; omega) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (by simp only [fTlen]; omega) (by decide)).symm

/-- The number of `V`s in a candidate: `⌈Q / D⌉`. -/
abbrev RfcHash.nV (P : RfcHash) : Nat := (P.Q + P.H.D - 1) / P.H.D

theorem nV_lt (P : RfcHash) (j : Nat) : j + 1 < P.nV ↔ (j + 1) * P.H.D < P.Q := by
  obtain ⟨-, -, -, -, -, -, hD16, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  rw [RfcHash.nV, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), Nat.succ_mul (j + 1)]
  omega

theorem nV_facts (P : RfcHash) : 1 ≤ P.nV ∧ P.nV * P.H.D ≤ P.Q + P.H.D - 1 ∧ P.Q ≤ P.nV * P.H.D := by
  obtain ⟨-, -, -, -, -, -, hD16, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  have e₁ := Nat.div_mul_le_self (P.Q + P.H.D - 1) P.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.H.D - 1) (show 0 < P.H.D by omega)
  have e₃ : 1 ≤ P.nV := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  simp only [RfcHash.nV] at e₃ ⊢
  generalize (P.Q + P.H.D - 1) / P.H.D = N at e₁ e₂ e₃ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  omega

/-- RFC 6979's number of blocks is `⌈Q / D⌉`. -/
theorem nV_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = P.nV := by
  obtain ⟨-, -, -, -, -, -, hD16, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  have hl := P.R.nBits_len
  have e₁ := Nat.div_mul_le_self (P.Q + P.H.D - 1) P.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.H.D - 1) (show 0 < P.H.D by omega)
  rw [Spec.Ecdsa.Rfc6979.blocks]
  simp only [RfcHash.nV, RfcHash.Q] at e₁ e₂ hQ8 ⊢
  generalize (P.R.E.C.len + P.H.D - 1) / P.H.D = N at e₁ e₂ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  have h₁ : N * (8 * P.H.D) = 8 * (N * P.H.D) := Nat.mul_left_comm _ _ _
  have h₂ : (N + 1) * (8 * P.H.D) = 8 * (N * P.H.D) + 8 * P.H.D := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The loop: `nV` `V`s. -/
theorem loop_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {u : State}
    (hI : CI P L g m₀ t₀ K V₀ 0 u) :
    WP isa (.loop (cfgOf P).candStep (.nonzero .x .x12)) u (CI P L g m₀ t₀ K V₀ P.nV) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, -, -, hD64, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  refine WP.loop (M := isa) (fun (n : Nat) (s : State) => ∃ j, n = P.nV - j ∧ j < P.nV ∧ CI P L g m₀ t₀ K V₀ j s)
    ?_ (P.nV - 0) u ⟨0, rfl, hN1, hI⟩
  rintro n s ⟨j, rfl, hj, hIj⟩
  have hb : (j + 1) * P.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega) (Nat.le_refl P.H.D)) (by omega)
  refine WP.mono (step_ok hL hT hb hIj) fun s' ⟨hI', hcf⟩ => ?_
  by_cases hlt : j + 1 < P.nV
  · exact .inr ⟨by rw [eval_nonzero, hcf, decide_eq_true ((nV_lt P j).mp hlt)],
      P.nV - (j + 1), by omega, j + 1, rfl, hlt, hI'⟩
  · refine .inl ⟨by rw [eval_nonzero, hcf, decide_eq_false (fun h => hlt ((nV_lt P j).mpr h))], ?_⟩
    rw [show P.nV = j + 1 by omega]; exact hI'

/-! ## The candidate -/

/-- `T` empty: no `V`s yet. -/
theorem tInit_ci (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.block Cfg.tInit) t (CI P L g m₀ t (kOf P L t.mem) (vOf P L t.mem) 0) := by
  have he := L.he
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  refine WP.mono (tInit_ok hL hc) fun u₀ ⟨hc₀, hf₀, hl₀⟩ => ?_
  have kv0 : ∀ {o : Nat}, 16 ≤ o → o + P.H.D ≤ 144 →
      Spec.Sha256.bytesAt u₀.mem (L.B + BitVec.ofNat 64 o) P.H.D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 o) P.H.D := fun h₁ h₂ =>
    bytesAt_frame hf₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [fTlen]; omega)) (by omega) (by simp only [fTlen]; omega))
      (by omega)
  exact
    { ctx := hc₀
      frame := hf₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨L.B, 152⟩, by simp, Offset.sub_base _ (by decide)⟩
      k := kv0 (by decide) (by omega)
      v := kv0 (by decide) (by omega)
      len := by rw [hl₀, Nat.zero_mul]
      t := by simp [Spec.Sha256.bytesAt, Spec.Ecdsa.Rfc6979.genT]
      saved := hS.frame hf₀ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.stk_scr (by simp only [fTlen]; omega) (by decide)).symm }


theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- The candidate: `nV` successive `V = HMAC_K(V)`, and `k`, whose number is
`bits2int` of their concatenation, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg P L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
          (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 ∧
      SavedK P L u.mem (kOf P L t.mem) := by
  have he := L.he
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hl := P.R.nBits_len
  obtain ⟨-, hND, hQN⟩ := nV_facts P
  rw [Cfg.cand]
  refine WP.seq (WP.mono (tInit_ci hL hc hS) fun u₀ hI0 => ?_)
  refine WP.seq (WP.mono (loop_ok hL hT hI0) fun u₁ hI₁ => ?_)
  have hTl := genT_length P (kOf P L t.mem) P.nV (vOf P L t.mem)
  have hbits : Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
      (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (kArg P L) P.Q) >>> P.R.sh := by
    rw [Spec.Ecdsa.Rfc6979.bits2int, Rfc6979.hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
      (by rw [hTl]; exact hQN),
      show (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
        Spec.Sha256.bytesAt u₁.mem (kArg P L) (P.nV * P.H.D) from hI₁.t.symm,
      ← bytesAt_take _ _ hQN, show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh by rw [hl.2.2]]
  cases hb : P.R.big
  · have hsh : P.R.sh = 0 := by have := (P.R.sizesA hb).2.2.1; omega
    rw [show (cfgOf P).candTop = .block [] by simp only [Cfg.candTop, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false], WP.block_nil_iff]
    exact ⟨hI₁.ctx, hI₁.frame, hI₁.k, hI₁.v, by rw [hbits, hsh, Nat.shiftRight_zero], hI₁.saved⟩
  · have hsh8 : P.R.sh < 8 := by omega
    have hsh0 : P.R.sh ≠ 0 := by have := (P.R.sizesW hb); omega
    refine WP.mono (candTop_ok hL hb hsh0 hsh8 hI₁.ctx) fun u ⟨hcu, hf, hbu⟩ => ?_
    have kv : ∀ {o : Nat}, 16 ≤ o → o + P.H.D ≤ 144 →
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 o) P.H.D =
          Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) P.H.D := fun h₁ h₂ =>
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
      · exact ⟨⟨L.B + BitVec.ofNat 64 (16 + fT), 136⟩, by simp, Region.sub_prefix (by omega)⟩
    · rw [show kArg P L = L.B + BitVec.ofNat 64 (16 + fT) from rfl, hbu, hbits,
        Rfc6979.ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
          have := Rfc6979.ofBytes_lt (Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (16 + fT)) P.Q)
          rwa [length_bytesAt] at this))]
    · refine hI₁.saved.frame hf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
      · exact (hL.stk_scr (by simp only [fT]; omega) (by decide)).symm

end VG.Proof.Ecdsa.Rfc6979.AArch64
