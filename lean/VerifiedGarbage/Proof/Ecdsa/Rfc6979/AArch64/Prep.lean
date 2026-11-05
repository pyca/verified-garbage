module
-- separate module: its proofs (the buffers X and h) build in parallel with `Steps`, which `Cand` also imports

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Wide
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on AArch64: the digest into `X`

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Prep.lean`): the byte loop
`cpLoop`, `x13` bytes from `x11` to `x12` with `Ctx` kept, for a destination
the code may write apart from the source (`cp_ok`), and `X` (`prepX_ok`):
`Q - m` zero bytes, then the digest's first `m = min(D, Q)`, its length the
smaller of the frame's `D` and `Q` (`min_ok`, by `subs` and `csel`); and, if
`big`, the digest for `core` (`prepC_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.RsaOaep.AArch64 (count_loop counter_step counter_ne carry_sub read_one byte64 byte_rt64 write1_apply)
open VG.Proof.Mgf1 (ifp ifn)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## `X` -/

/-- `subs x10, x13, x9; csel x13, x9, x13`: the smaller of the two in `x13`. -/
theorem min_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h13 : u.gpr .x13 = BitVec.ofNat 64 a) (h9 : u.gpr .x9 = BitVec.ofNat 64 b) :
    WP isa (.block [.subs .x .x10 .x13 .x9, .csel .x .x13 .x9 .x13]) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .x13 = BitVec.ofNat 64 (min a b) ∧
      ∀ r, r ≠ .x10 → r ≠ .x13 → u'.gpr r = u.gpr r := by
  have hta : (u.gpr .x13).toNat = a := by rw [h13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have htb : (u.gpr .x9).toNat = b := by rw [h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.mem_addWithCarry, RegUpd.gpr_write, RegUpd.mem_write,
    reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  rw [carry_sub, hta, htb]
  refine ⟨hc.regs hL (by atriv) (by atriv) (by atriv) (by atriv) (fun r hr _ => ?_) (by atriv), by atriv, ?_,
    fun r h₁ h₂ => ?_⟩
  · simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, ne_cs hr (by decide : Reg.x13 ∉ preserved),
      ne_cs hr (by decide : Reg.x10 ∉ preserved), ite_false]
  · by_cases h : b ≤ a
    · simp only [h, decide_true, ite_true, h9, Nat.min_eq_right h]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false, h13, Nat.min_eq_left (show a ≤ b by omega)]
  · simp only [h₁, h₂, ite_false]

/-- `x12 = sp + o - x13` and the digest in `x11`. -/
theorem xTail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho : o < 4096) :
    WP isa (.block [.addSp .x12 o, .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest]) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .x12 = L.B + BitVec.ofNat 64 (16 + o) - u.gpr .x13 ∧ u'.gpr .x11 = L.dg ∧
      ∀ r, r ≠ .x11 → r ≠ .x12 → u'.gpr r = u.gpr r := by
  rw [show ([.addSp .x12 o, .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] : List Instr) =
    Cfg.fr .x12 o ++ [.sub .x .x12 .x12 .x13] ++ [.ldrSp .x11 fDigest] from rfl, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x12) (by decide) ho) fun u₁ h₁ => ?_
  refine WP.mono (show WP isa (.block [.sub .x .x12 .x12 .x13]) u₁
      (Upd L g m₀ u₁ .x12 (u₁.gpr .x12 - u₁.gpr .x13)) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
      Option.some.injEq, exists_eq_left']
    exact ⟨h₁.ctx.set hL (d := .x12) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl,
      rfl, by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _,
      fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩) fun u₂ h₂ => ?_
  refine WP.mono (ldF_ok hL h₂.ctx (d := .x11) (by decide) (o := fDigest) (by simp only [fDigest]; have := L.he; omega)
    rfl) fun u₃ h₃ => ?_
  refine ⟨h₃.ctx, by rw [h₃.mem, h₂.mem, h₁.mem], by rw [h₃.keep _ (by decide), h₂.val, h₁.val,
    h₁.keep _ (by decide)], by rw [h₃.val, h₂.mem, h₁.mem]; exact hc.pDg, fun r a b => by
    rw [h₃.keep _ a, h₂.keep _ b, h₁.keep _ b]⟩

theorem sub_min (B : Addr) {a b c : Nat} (h : c ≤ b) :
    B + BitVec.ofNat 64 (a + b) - BitVec.ofNat 64 c = B + BitVec.ofNat 64 (a + (b - c)) := by
  rw [show a + b = a + (b - c) + c by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- The arguments of `X`'s copy: `X` cleared, `x13 = m = min(D, Q)`, the
digest in `x11` and `X + Q - m` in `x12`. -/
theorem xArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xArgs) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fX)) 72 = List.replicate 72 0 ∧
      u.gpr .x13 = BitVec.ofNat 64 (min P.H.D P.Q) ∧
      u.gpr .x12 = L.B + BitVec.ofNat 64 (16 + fX + (P.Q - min P.H.D P.Q)) ∧ u.gpr .x11 = L.dg := by
  have he := L.he
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.xArgs, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fX) (by decide) (by simp only [fX]; omega) (by decide) hc)
    fun u₁ ⟨hc₁, _, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.ldrSp .x13 fDl, .movz .x .x9 (BitVec.ofNat 16 P.Q) 0, .subs .x .x10 .x13 .x9,
      .csel .x .x13 .x9 .x13, .addSp .x12 (fX + P.Q), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] : List Instr) =
    [.ldrSp .x13 fDl] ++ [.movz .x .x9 (BitVec.ofNat 16 P.Q) 0] ++ [.subs .x .x10 .x13 .x9, .csel .x .x13 .x9 .x13] ++
      [.addSp .x12 (fX + P.Q), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldD_ok hL hT hc₁ (d := .x13) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (movz_ok hL h₂.ctx (d := .x9) (by decide) (n := P.Q) (by omega)) fun u₃ h₃ => ?_
  have h13₃ : u₃.gpr .x13 = BitVec.ofNat 64 P.H.D := by rw [h₃.keep _ (by decide), h₂.val]
  refine WP.mono (min_ok hL h₃.ctx (a := P.H.D) (b := P.Q) (by omega) (by omega) h13₃ h₃.val)
    fun u₄ ⟨hc₄, hm₄, h13₄, hg₄⟩ => ?_
  refine WP.mono (xTail_ok hL hc₄ (o := fX + P.Q) (by simp only [fX]; omega))
    fun u₅ ⟨hc₅, hm₅, h12₅, h11₅, hg₅⟩ => ?_
  have hm : min P.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  rw [h13₄, ← Nat.add_assoc, sub_min _ hm] at h12₅
  have hm₅' : u₅.mem = u₁.mem := by rw [hm₅, hm₄, h₃.mem, h₂.mem]
  exact ⟨hc₅, hm₅' ▸ hf₁, hm₅' ▸ hb₁, by rw [hg₅ _ (by decide) (by decide), h13₄], h12₅, h11₅⟩

/-- `X`, the `Q` bytes at `fX`: `Q - m` zero bytes, then the digest's first
`m = min(D, Q)`. -/
theorem prepX_ok (hL : L.Ok) (hT : TabL P L) (hdn : P.H.D ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepX t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fX)) P.Q =
        List.replicate (P.Q - min P.H.D P.Q) 0 ++ Spec.Sha256.bytesAt t.mem L.dg (min P.H.D P.Q) := by
  have he := L.he
  have hnb := hL.nB
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  rw [Cfg.prepX]
  refine WP.seq (WP.mono (xArgs_ok hL hT hc) fun u₅ ⟨hc₅, hf₁, hb₁, h13₅, h12₅, h11₅⟩ => ?_)
  have hm : min P.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  have hm8 : 8 ≤ min P.H.D P.Q := by omega
  refine WP.mono (cp_ok hL hc₅ (p := L.B + BitVec.ofNat 64 (16 + fX + (P.Q - min P.H.D P.Q))) (q := L.dg)
      (n := min P.H.D P.Q) (by omega) (by omega) h13₅ h12₅ h11₅ ?_ (hc₅.inFrW (by omega) (by simp only [fX]; omega))
      (safe_high L (by simp only [fX]; omega) (by simp only [fX]; omega))
      (fun i hi => hc₅.inDg (o := i) (n := 1) (by omega) (by omega))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 256 + 8 * L.e) (by simp only [fX]; omega) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := dn) (by omega) (by omega))))
    fun u ⟨hc', _, hf, hb⟩ => ?_
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + fX + _) (by simp only [fX]; omega),
      Nat.mod_eq_of_lt (by simp only [fX]; omega)]
    simp only [fX]; omega
  have hdn' : min P.H.D P.Q ≤ dn := by omega
  have hdg : Spec.Sha256.bytesAt u₅.mem L.dg (min P.H.D P.Q) = Spec.Sha256.bytesAt t.mem L.dg (min P.H.D P.Q) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 16 + fX) (n := 72) (k := 256 + 8 * L.e)
        (by simp only [fX]; omega) a h₂) (Region.sub_prefix hdn' a h₁)) (by omega)
  refine ⟨hc', hf₁.trans ?_, ?_⟩
  · exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by simp only [fX]; omega)⟩
  · rw [show P.Q = (P.Q - min P.H.D P.Q) + min P.H.D P.Q by omega, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, hb, ← show P.Q = (P.Q - min P.H.D P.Q) + min P.H.D P.Q by omega,
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega)) (by simp only [fX]; omega) (by simp only [fX]; omega)) (by omega),
      hdg]
    rw [bytesAt_take _ _ (k := 72) (by omega), hb₁, List.take_replicate, Nat.min_eq_left (by omega)]

/-! ## P-521's digest for `core` -/

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- If `big`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem prepC_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) (hdn : P.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepC t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (16 + fXc), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fXc)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.H.D) * 2 ^ P.R.sh) := by
  have he := L.he
  have hnb := hL.nB
  obtain ⟨-, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hsl := P.R.nBits_len
  have hnb5 := (P.R.sizesW hW).2.2
  have hsh8 : P.R.sh < 8 := by simp only [RfcHash.Q] at hQ66; omega
  have hsh1 : 1 ≤ P.R.sh := by simp only [RfcHash.Q] at hQ66; omega
  have hlen : (cfgOf P).len = P.Q := rfl
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.prepC]
  refine WP.seq ?_
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fXc) (by decide) (by simp only [fXc]; omega) (by decide) hc)
    fun u₁ ⟨hc₁, _, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.ldrSp .x13 fDl, .addSp .x12 (fXc + P.Q - 1), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] :
      List Instr) = [.ldrSp .x13 fDl] ++ [.addSp .x12 (fXc + P.Q - 1), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest]
      from rfl, WP.block_append_iff]
  refine WP.mono (ldD_ok hL hT hc₁ (d := .x13) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (xTail_ok hL h₂.ctx (o := fXc + P.Q - 1) (by simp only [fXc]; omega))
    fun u₃ ⟨hc₃, hm₃, h12₃, h11₃, hg₃⟩ => ?_
  have hx : 16 + (fXc + P.Q - 1 - P.H.D) = 16 + fXc + (P.Q - 1 - P.H.D) := by omega
  rw [h₂.val, show 16 + (fXc + P.Q - 1) = 16 + (fXc + P.Q - 1) from rfl, sub_min _ (by omega), hx] at h12₃
  have hm₁ : u₃.mem = u₁.mem := by rw [hm₃, h₂.mem]
  have hdg : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 16 + fXc) (n := 72) (k := 256 + 8 * L.e)
        (by simp only [fXc]; omega) a h₂) (Region.sub_prefix hdn a h₁)) (by omega)
  refine WP.seq (WP.mono (cp_ok hL hc₃ (p := L.B + BitVec.ofNat 64 (16 + fXc + (P.Q - 1 - P.H.D))) (q := L.dg)
      (n := P.H.D) (by omega) (by omega) (by rw [hg₃ _ (by decide) (by decide), h₂.val])
      h12₃ h11₃ ?_ (hc₃.inFrW (by omega) (by simp only [fXc]; omega))
      (safe_high L (by simp only [fXc]; omega) (by simp only [fXc]; omega))
      (fun i hi => hc₃.inDg (o := i) (n := 1) (by omega) (by omega))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 256 + 8 * L.e) (by simp only [fXc]; omega) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := dn) (by omega) (by omega))))
    fun u₄ ⟨hc₄, _, hf₄, hb₄⟩ => ?_)
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + fXc + _) (by simp only [fXc]; omega),
      Nat.mod_eq_of_lt (by simp only [fXc]; omega)]
    simp only [fXc]; omega
  rw [hsc]
  refine WP.mono (conv_ok hL hW hc₄ (o := fXc) (s := 8 - P.R.sh) (by decide) (by decide) (by decide) (by omega)
    (by omega)) fun u₆ ⟨hc₆, hf₆, hb₆⟩ => ?_
  refine ⟨hc₆, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hm₁ ▸ hf₄.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans
      (hf₆.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by simp only [fXc]; omega)
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    have hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (16 + fXc + a)) n =
        List.replicate n 0 := fun a n han => by
      have h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 (16 + fXc)) (n := a + n) (k := 72) (by omega)
      rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
    have hY : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (16 + fXc)) P.Q =
        List.replicate (P.Q - 1 - P.H.D) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.H.D ++ List.replicate 1 0) := by
      have e := Proof.Hmac.Common.bytesAt_add u₄.mem (L.B + BitVec.ofNat 64 (16 + fXc)) (P.Q - 1 - P.H.D)
        (P.H.D + 1)
      have e' := Proof.Hmac.Common.bytesAt_add u₄.mem
        (L.B + BitVec.ofNat 64 (16 + fXc) + BitVec.ofNat 64 (P.Q - 1 - P.H.D)) P.H.D 1
      rw [show P.Q - 1 - P.H.D + (P.H.D + 1) = P.Q by omega] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      have p₁ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (16 + fXc)) (P.Q - 1 - P.H.D) =
          List.replicate (P.Q - 1 - P.H.D) 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega)) (by simp only [fXc]; omega) (by simp only [fXc]; omega))
          (by omega), hm₁]
        have := hz 0 (P.Q - 1 - P.H.D) (by omega)
        rwa [Nat.add_zero] at this
      have p₃ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (16 + fXc + (P.Q - 1 - P.H.D) + P.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by omega)) (by simp only [fXc]; omega) (by simp only [fXc]; omega))
          (by omega), hm₁, show 16 + fXc + (P.Q - 1 - P.H.D) + P.H.D = 16 + fXc + (P.Q - 1 - P.H.D + P.H.D) by omega]
        exact hz (P.Q - 1 - P.H.D + P.H.D) 1 (by omega)
      rw [e, e', hb₄, hm₁, hdg, p₁, p₃]
    rw [hb₆, hY, Rfc6979.ofBytes_zeros, Rfc6979.ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

end VG.Proof.Ecdsa.Rfc6979.AArch64
