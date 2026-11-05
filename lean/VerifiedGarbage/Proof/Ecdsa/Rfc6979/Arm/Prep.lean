module

import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Wide
public import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: the digest into `X`

The byte loop `copyLoop` (`Proof/AesGcm/Arm/Loops.lean`), `r3` bytes from
`r1` to `r2` with `Ctx` kept, for a destination the code may write apart
from the source (`cp_ok`); zero words in the frame (`zeroN_ok`); and `X`
(`prepX_ok`): `Q - m` zero bytes, then the digest's first `m = min(D, Q)`,
its length the smaller of the table's `D` and `Q`, computed without a branch
(`min_ok`: `Q + ((D - Q) & mask)`, the mask all ones iff `D - Q` borrows).
If `big`, `core`'s digest (`prepC_ok`): `Q - 1 - D` zero bytes, the digest
and a zero byte, shifted right by `8 - sh` bits, which is the digest's
integer shifted left by `sh` bits.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.AesGcm.Arm (copyLoop imm)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_str op2_reg op2_imm dpVal)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## A byte loop -/

/-- `n` bytes from `q` (`r1`) to `p` (`r2`), `n` in `r3`, by `copyLoop`:
`Ctx` kept, for a destination the code may write apart from the source. -/
theorem cp_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {p q : BitVec 32} {n : Nat} (hn : 0 < n)
    (hn' : n < 2 ^ 32) (h1 : u.gpr .r1 = q) (h2 : u.gpr .r2 = p) (h3 : u.gpr .r3 = BitVec.ofNat 32 n)
    (fq : q.toNat + n ≤ 2 ^ 32) (fp : p.toNat + n ≤ 2 ^ 32)
    (hr : ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨State.addr q, n⟩ R)
    (hw : ∃ R ∈ [L.FR, L.OUT, L.SCR], Within ⟨State.addr p, n⟩ R) (hs : Safe L ⟨State.addr p, n⟩)
    (hd : (⟨State.addr q, n⟩ : Region).Disjoint ⟨State.addr p, n⟩) :
    WP isa copyLoop u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → u'.gpr r = u.gpr r) ∧
      Frame [⟨State.addr p, n⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (State.addr p) n = Spec.Sha256.bytesAt u.mem (State.addr q) n := by
  have pre : VG.Proof.AesGcm.Arm.LoopPre u q p n :=
    ⟨h1, h2, h3, hn, hn', fq, fp, hc.covers fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact hr,
      hc.coversW fun r hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hw, hd⟩
  refine WP.mono_syms (VG.Proof.AesGcm.Arm.copyLoop_ok u pre) fun u' ⟨hm, O⟩ sy => ?_
  have hlen : (Spec.Aes.bytesAt u.mem (State.addr q) n).length = n := by simp [Spec.Aes.bytesAt]
  have hf : Frame [⟨State.addr p, n⟩] u.mem u'.mem := by
    rw [hm]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hlen]; exact Region.contains_self _ _)
  have hp : ∀ r ∈ ptrRegs, r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by decide
  refine ⟨hc.keep hL O.rd O.wr O.sp (fun r hr' => O.other r (hp r hr').1 (hp r hr').2.1 (hp r hr').2.2.1
      (hp r hr').2.2.2.1 (hp r hr').2.2.2.2) hf
      (fun r hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hs) sy,
    O.other, hf, ?_⟩
  rw [hm]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self u.mem (State.addr p) (Spec.Aes.bytesAt u.mem (State.addr q) n)
    (by rw [hlen]; omega_arith)
  rw [hlen] at this
  exact this

/-! ## Zero words in the frame -/

theorem zeroN_raw (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (h0 : u.gpr .r0 = 0) : ∀ k, o + 4 * k ≤ 468 →
    WP isa (.block ((List.range k).map fun j => .str .r0 .r8 (o + 4 * j))) u
      fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧
        Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 4 * k⟩] u.mem u'.mem ∧
        ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (24 + o + 4 * j)) 32 = 0
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroN_raw hL hc h0 k (by omega_arith)) fun u₁ ⟨hrd, hwr, hsp, hg, hf, hv⟩ => ?_
    have e₁ : State.addr (L.fp + BitVec.ofNat 32 (o + 4 * k)) = L.B + BitVec.ofNat 64 (24 + o + 4 * k) := by
      rw [hL.fpA (by omega_arith), Nat.add_assoc]
    refine wp_strS (a := L.B + BitVec.ofNat 64 (24 + o + 4 * k)) (by omega_arith) (by rw [hg, hc.r8]; exact e₁)
      (by rw [hwr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u₂ v₂ => WP.block_nil ?_
    have sep : ∀ x y, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 536 → y + 4 ≤ 536 →
        Mem.Sep (L.B + BitVec.ofNat 64 x) (32 / 8) (L.B + BitVec.ofNat 64 y) (32 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega_arith) (by omega_arith)
    have hm₂ : u₂.mem = u₁.mem.writeW (L.B + BitVec.ofNat 64 (24 + o + 4 * k)) (0 : BitVec 32) := by
      rw [v₂.mem, hg, h0]
    refine ⟨by rw [v₂.rd, hrd], by rw [v₂.wr, hwr], by rw [v₂.sp, hsp], by rw [v₂.gpr, hg], ?_, fun j hj => ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)
      · rw [hm₂]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    · rw [hm₂]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        exact hv j hj
      · rw [Mem.readW_writeW_self32]

/-- `k` zero words at the frame's `o`, through `r0`: their bytes are zero. -/
theorem zeroN_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {k o : Nat} (ho : o + 4 * k ≤ 468) :
    WP isa (.block (Cfg.zeroN k o)) u fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 4 * k⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) (4 * k) = List.replicate (4 * k) 0 := by
  rw [Cfg.zeroN]
  refine wp_movS (op2_imm (by decide)) fun u₁ v₁ => ?_
  have hc₁ := hc.upd v₁ (by decide)
  refine WP.mono_syms (zeroN_raw hL hc₁ (o := o) v₁.gpr k ho) fun u' ⟨hrd, hwr, hsp, hg, hf, hv⟩ sy => ?_
  refine ⟨hc₁.keep hL hrd hwr hsp (fun r _ => by rw [hg]) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)) sy,
    fun r hr => by rw [hg, v₁.other _ hr], by rw [← v₁.mem]; exact hf, ?_⟩
  rw [bytesAt_of_readW _ _ (0 : BitVec 32) fun j hj => by rw [Offset.add_add]; exact hv j hj]
  exact List.eq_replicate_iff.mpr ⟨by simp, fun b hb => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb; simp⟩

/-! ## `X` -/

theorem min_val (D Q : Nat) (hD : D < 2 ^ 32) (hQ : Q < 2 ^ 32) :
    BitVec.ofNat 32 Q + ((BitVec.ofNat 32 D - BitVec.ofNat 32 Q) &&&
      (0#32 + 0#32 + (if decide ((BitVec.ofNat 32 Q).toNat ≤ (BitVec.ofNat 32 D).toNat) = true then 1 else 0) -
        1#32)) = BitVec.ofNat 32 (min D Q) := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hQ]
  by_cases h : Q ≤ D
  · simp only [h, decide_true, ↓reduceIte, Nat.min_eq_right h]
    rw [show (0#32 + 0#32 + 1 - 1#32 : BitVec 32) = 0#32 by decide, BitVec.and_zero, BitVec.add_zero]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.min_eq_left (by omega_arith : D ≤ Q)]
    rw [show (0#32 + 0#32 + 0 - 1#32 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes,
      BitVec.add_comm, BitVec.sub_add_cancel]

/-- `r3 = min(D, Q)` (`r0 = Q` and `r7`, `r12` changed). -/
theorem min_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {is : List Instr} {Q' : State → Prop}
    (k : ∀ u', Ctx L g m₀ u' → u'.mem = u.mem → u'.gpr .r3 = BitVec.ofNat 32 (min P.F.H.D P.Q) →
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r7 → r ≠ .r12 → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q') :
    WP isa (.block ([.ldr .r3 .r6 tD, .movw .r0 (BitVec.ofNat 16 P.Q), .subs .r12 .r3 (.reg .r0),
      .mov .r7 (imm 0), .adc .r7 .r7 (imm 0), .dp .sub .r7 .r7 (imm 1), .dp .and .r12 .r12 (.reg .r7),
      .dp .add .r3 .r0 (.reg .r12)] ++ is)) u Q' := by
  simp only [List.cons_append, List.nil_append]
  have hD : P.F.H.D < 2 ^ 32 := by anums
  have hQ : P.Q < 2 ^ 16 := by anums
  refine ldD_ok hL hc (d := .r3) (by decide) fun u₁ c₁ m₁ v₁ k₁ => ?_
  rw [hT.1] at v₁
  refine movw_ok c₁ (d := .r0) (by decide) hQ fun u₂ c₂ m₂ v₂ k₂ => ?_
  refine wp_subsC (op2_reg _ _) fun u₃ v₃ c₃ => ?_
  have c₃' := c₂.upd v₃ (by decide)
  refine wp_movC (op2_imm (by decide)) fun u₄ v₄ c₄ => wp_adc (op2_imm (by decide)) fun u₅ v₅ => ?_
  refine wp_dpS (op2_imm (by decide)) fun u₆ v₆ => wp_dpS (op2_reg _ _) fun u₇ v₇ => ?_
  refine wp_dpS (op2_reg _ _) fun u₈ v₈ => ?_
  have c₈ := (((((c₃'.upd v₄ (by decide)).upd v₅ (by decide)).upd v₆ (by decide)).upd v₇ (by decide)).upd v₈ (by decide))
  refine k u₈ c₈ (by rw [v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, m₂, m₁]) ?_ fun r h0 h3 h7 h12 => ?_
  · have e12 : u₃.gpr .r12 = BitVec.ofNat 32 P.F.H.D - BitVec.ofNat 32 P.Q := by
      rw [v₃.gpr, k₂ _ (by decide), v₁, v₂]
    have ec : u₄.c = decide ((BitVec.ofNat 32 P.Q).toNat ≤ (BitVec.ofNat 32 P.F.H.D).toNat) := by
      rw [c₄, c₃, v₂, k₂ _ (by decide), v₁]
    have e7₆ : u₆.gpr .r7 = 0#32 + 0#32 + (if u₄.c then 1 else 0) - 1#32 := by
      rw [v₆.gpr, dpVal, v₅.gpr, v₄.gpr]
    have e12₆ : u₆.gpr .r12 = u₃.gpr .r12 := by
      rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide)]
    have e12₇ : u₇.gpr .r12 = u₆.gpr .r12 &&& u₆.gpr .r7 := by rw [v₇.gpr, dpVal]
    have e0₇ : u₇.gpr .r0 = BitVec.ofNat 32 P.Q := by
      rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
        v₃.other _ (by decide), v₂]
    rw [v₈.gpr, dpVal, e0₇, e12₇, e12₆, e7₆, e12, ec]
    exact min_val _ _ hD (by omega_arith)
  · rw [v₈.other _ h3, v₇.other _ h12, v₆.other _ h7, v₅.other _ h7, v₄.other _ h7, v₃.other _ h12, k₂ _ h0,
      k₁ _ h3]

theorem addr_shuffle (a f b : BitVec 32) : a + f - b = f + (a - b) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_comm a f, BitVec.add_assoc]

/-- `r2 = fp + (a - n)` for `r3 = n`, and `r1 = digest`, from the frame's slot. -/
theorem dstArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a n : Nat} (ha : a < 2 ^ 16) (hn : n ≤ a)
    (h3 : u.gpr .r3 = BitVec.ofNat 32 n) :
    WP isa (.block [.movw .r2 (BitVec.ofNat 16 a), .dp .add .r2 .r2 (.reg .r8), .dp .sub .r2 .r2 (.reg .r3),
      .ldr .r1 .r8 fDigest]) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
        u'.gpr .r2 = L.fp + BitVec.ofNat 32 (a - n) ∧ u'.gpr .r1 = L.dg ∧ u'.gpr .r3 = BitVec.ofNat 32 n ∧
        ∀ r, r ≠ .r1 → r ≠ .r2 → u'.gpr r = u.gpr r := by
  refine movw_ok hc (d := .r2) (by decide) ha fun u₁ c₁ m₁ v₁ k₁ => ?_
  refine wp_dpS (op2_reg _ _) fun u₂ v₂ => wp_dpS (op2_reg _ _) fun u₃ v₃ => ?_
  have c₃ := (c₁.upd v₂ (by decide)).upd v₃ (by decide)
  refine frLd_ok hL c₃ (d := .r1) (by decide) (o := fDigest) (by decide) fun u₄ c₄ m₄ v₄ k₄ => WP.block_nil ?_
  refine ⟨c₄, by rw [m₄, v₃.mem, v₂.mem, m₁], ?_, by rw [v₄]; exact c₃.pDg, ?_, fun r h1 h2 => ?_⟩
  · rw [k₄ _ (by decide), v₃.gpr, dpVal, v₂.gpr, dpVal, v₁, v₂.other .r3 (by decide),
      k₁ .r3 (by decide), k₁ .r8 (by decide), h3, hc.r8, addr_shuffle, VG.Proof.AesGcm.Arm.ofNat_sub32 hn (by omega_arith)]
  · rw [k₄ _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), k₁ _ (by decide), h3]
  · rw [k₄ _ h1, v₃.other _ h2, v₂.other _ h2, k₁ _ h2]

/-- The arguments of `X`'s copy: `X` cleared, `r3 = m = min(D, Q)`, the
digest in `r1`, `X + Q - m` in `r2`. -/
theorem xArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xArgs) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 216, 68⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 216) 68 = List.replicate 68 0 ∧
      u.gpr .r3 = BitVec.ofNat 32 (min P.F.H.D P.Q) ∧
      u.gpr .r2 = L.fp + BitVec.ofNat 32 (fX + P.Q - min P.F.H.D P.Q) ∧ u.gpr .r1 = L.dg := by
  rw [Cfg.xArgs, WP.block_append_iff]
  refine WP.mono (zeroN_ok hL hc (k := 17) (o := fX) (by decide)) fun u₁ ⟨c₁, _, f₁, b₁⟩ => ?_
  refine (min_ok hL hT c₁ (is := [.movw .r2 (BitVec.ofNat 16 (fX + P.Q)), .dp .add .r2 .r2 (.reg .r8),
      .dp .sub .r2 .r2 (.reg .r3), .ldr .r1 .r8 fDigest]) fun u₂ c₂ m₂ v₂ _ => ?_ : _)
  refine WP.mono (dstArgs_ok hL c₂ (a := fX + P.Q) (n := min P.F.H.D P.Q) (by simp only [fX]; anums)
    (by simp only [fX]; omega_arith) v₂) fun u₃ ⟨c₃, m₃, h2, h1, h3, _⟩ => ?_
  have hm : u₃.mem = u₁.mem := by rw [m₃, m₂]
  exact ⟨c₃, hm ▸ f₁, hm ▸ b₁, h3, h2, h1⟩

/-- `X`, the `Q` bytes at `fX`: `Q - m` zero bytes, then the digest's first
`m = min(D, Q)`. -/
theorem prepX_ok (hL : L.Ok) (hT : TabL P L) (hdn : P.F.H.D ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepX t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 216, 68⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 216) P.Q =
        List.replicate (P.Q - min P.F.H.D P.Q) 0 ++ Spec.Sha256.bytesAt t.mem (State.addr L.dg) (min P.F.H.D P.Q) := by
  have hb := hL.B_fit
  have ng := hL.ng
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  have : fX = 192 := rfl
  rw [Cfg.prepX]
  refine WP.seq (WP.mono (xArgs_ok hL hT hc) fun u₅ ⟨hc₅, hf₁, hb₁, h3, h2, h1⟩ => ?_)
  have hm : min P.F.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  have hm16 : 16 ≤ min P.F.H.D P.Q := by omega_arith
  have hpa : State.addr (L.fp + BitVec.ofNat 32 (fX + P.Q - min P.F.H.D P.Q)) =
      L.B + BitVec.ofNat 64 (216 + (P.Q - min P.F.H.D P.Q)) := by
    rw [hL.fpA (by omega_arith)]; congr 2; omega_arith
  refine WP.mono (cp_ok hL hc₅ (p := L.fp + BitVec.ofNat 32 (fX + P.Q - min P.F.H.D P.Q)) (q := L.dg)
      (n := min P.F.H.D P.Q) (by omega_arith) (by omega_arith) h1 h2 h3 (by omega_arith)
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      ⟨L.DG, by simp, within_base _ (by omega_arith)⟩
      (by rw [hpa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact safe_low L (by omega_arith))
      (by rw [hpa]; exact (hL.stk_DG (d := 216 + (P.Q - min P.F.H.D P.Q)) (n := min P.F.H.D P.Q)
        (by omega_arith)).symm.sub_left (Region.sub_prefix (by omega_arith))))
    fun u ⟨hc', _, hf, hbt⟩ => ?_
  rw [hpa] at hf hbt
  have hdg : Spec.Sha256.bytesAt u₅.mem (State.addr L.dg) (min P.F.H.D P.Q) =
      Spec.Sha256.bytesAt t.mem (State.addr L.dg) (min P.F.H.D P.Q) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hL.stk_DG (d := 216) (n := 68) (by omega_arith)).symm.sub_left
        (Region.sub_prefix (by omega_arith)))) (by omega_arith)
  refine ⟨hc', hf₁.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)⟩), ?_⟩
  rw [show P.Q = (P.Q - min P.F.H.D P.Q) + min P.F.H.D P.Q by omega_arith, Proof.Hmac.Common.bytesAt_add,
    Offset.add_add, hbt, ← show P.Q = (P.Q - min P.F.H.D P.Q) + min P.F.H.D P.Q by omega_arith,
    bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith),
    hdg, bytesAt_take _ _ (k := 68) (by omega_arith), hb₁, List.take_replicate, Nat.min_eq_left (by omega_arith)]

/-! ## P-521's digest for `core` -/

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega_arith, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- If `big`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem prepC_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) (hdn : P.F.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepC t fun u => Ctx L g m₀ u ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 284, 68⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 284) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.F.H.D) * 2 ^ P.R.sh) := by
  have hb := hL.B_fit
  have ng := hL.ng
  obtain ⟨-, hQ66, -, hQD⟩ := P.sizesW hW
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  have hsl := P.R.nBits_len
  have hnb5 := (P.R.sizesW hW).2.2
  have hsh8 : P.R.sh < 8 := by simp only [RfcHash.Q] at hQ66; omega_arith
  have hsh1 : 1 ≤ P.R.sh := by simp only [RfcHash.Q] at hQ66; omega_arith
  have : fXc = 260 := rfl
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.prepC]
  refine WP.seq ?_
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zeroN_ok hL hc (k := 17) (o := fXc) (by decide)) fun u₁ ⟨c₁, _, f₁, b₁⟩ => ?_
  rw [show 24 + fXc = 284 from rfl, show 4 * 17 = 68 from rfl] at f₁ b₁
  refine ldD_ok hL c₁ (d := .r3) (by decide) fun u₂ c₂ m₂ v₂ _ => ?_
  rw [hT.1] at v₂
  refine WP.mono (dstArgs_ok hL c₂ (a := fXc + (cfgOf P).len - 1) (n := P.F.H.D) (by simp only [cfgOf_len]; anums)
    (by simp only [cfgOf_len]; omega_arith) v₂) fun u₃ ⟨c₃, m₃, h2, h1, h3, _⟩ => ?_
  rw [cfgOf_len] at h2
  have hm₁ : u₃.mem = u₁.mem := by rw [m₃, m₂]
  have hdg : Spec.Sha256.bytesAt u₁.mem (State.addr L.dg) P.F.H.D = Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.F.H.D :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hL.stk_DG (d := 284) (n := 68) (by omega_arith)).symm.sub_left (Region.sub_prefix hdn))) (by omega_arith)
  have hpa : State.addr (L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D)) =
      L.B + BitVec.ofNat 64 (284 + (P.Q - 1 - P.F.H.D)) := by
    rw [hL.fpA (by omega_arith)]; congr 2; omega_arith
  refine WP.seq (WP.mono (cp_ok hL c₃ (p := L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D)) (q := L.dg)
      (n := P.F.H.D) (by omega_arith) (by omega_arith) h1 h2 h3 (by omega_arith)
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      ⟨L.DG, by simp, within_base _ hdn⟩
      (by rw [hpa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact safe_low L (by omega_arith))
      (by rw [hpa]; exact (hL.stk_DG (d := 284 + (P.Q - 1 - P.F.H.D)) (n := P.F.H.D)
        (by omega_arith)).symm.sub_left (Region.sub_prefix hdn)))
    fun u₄ ⟨c₄, _, f₄, b₄⟩ => ?_)
  rw [hpa] at f₄ b₄
  rw [hsc]
  refine WP.mono (conv_ok hL hW c₄ (o := fXc) (s := 8 - P.R.sh) (by omega_arith) (by omega_arith) (by decide)
    (by omega_arith) (by omega_arith)) fun u₆ ⟨c₆, _, f₆, b₆⟩ => ?_
  refine ⟨c₆, ?_, ?_⟩
  · have g₁ : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 284, 68⟩] t.mem u₁.mem :=
      f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, sub_refl _⟩
    have g₄ : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 284, 68⟩] u₃.mem u₄.mem :=
      f₄.sub fun r hr => ⟨⟨L.B + BitVec.ofNat 64 284, 68⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩
    have g₆ : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 284, 68⟩] u₄.mem u₆.mem :=
      f₆.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_arith)⟩
    rw [hm₁] at g₄
    exact (g₁.trans g₄).trans g₆
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    have hz : ∀ a n, a + n ≤ 68 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (284 + a)) n =
        List.replicate n 0 := fun a n han => by
      have h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 284) (n := a + n) (k := 68) (by omega_arith)
      rw [b₁, List.take_replicate, Nat.min_eq_left (by omega_arith), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
    have hY : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 284) P.Q =
        List.replicate (P.Q - 1 - P.F.H.D) 0 ++ (Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.F.H.D ++
          List.replicate 1 0) := by
      have e := Proof.Hmac.Common.bytesAt_add u₄.mem (L.B + BitVec.ofNat 64 284) (P.Q - 1 - P.F.H.D)
        (P.F.H.D + 1)
      have e' := Proof.Hmac.Common.bytesAt_add u₄.mem
        (L.B + BitVec.ofNat 64 284 + BitVec.ofNat 64 (P.Q - 1 - P.F.H.D)) P.F.H.D 1
      rw [show P.Q - 1 - P.F.H.D + (P.F.H.D + 1) = P.Q by omega_arith] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      have p₁ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 284) (P.Q - 1 - P.F.H.D) =
          List.replicate (P.Q - 1 - P.F.H.D) 0 := by
        rw [bytesAt_frame f₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
          (by omega_arith), hm₁]
        have := hz 0 (P.Q - 1 - P.F.H.D) (by omega_arith)
        rwa [Nat.add_zero] at this
      have p₃ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (284 + (P.Q - 1 - P.F.H.D) + P.F.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame f₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
          (by omega_arith), hm₁, show 284 + (P.Q - 1 - P.F.H.D) + P.F.H.D = 284 + (P.Q - 1 - P.F.H.D + P.F.H.D) by
            omega_arith]
        exact hz (P.Q - 1 - P.F.H.D + P.F.H.D) 1 (by omega_arith)
      rw [e, e', b₄, hm₁, hdg, p₁, p₃]
    rw [show 24 + fXc = 284 from rfl] at b₆
    rw [b₆, hY, ofBytes_zeros, ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

end VG.Proof.Ecdsa.Rfc6979.Arm
