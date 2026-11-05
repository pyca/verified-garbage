module
-- separate module: its proofs (the buffers X and h) build in parallel with `Steps`, which `Cand` also imports

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Wide
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on x86 (32-bit): the digest into `X`

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Prep.lean`): `X` (`prepX_ok`):
`Q - m` zero bytes, then the digest's first `m = min(D, Q)`, its length the
smaller of the frame's `D` and `Q` (`min_ok`, by the borrow of `D - Q`, a
mask), copied by the byte loop (`cpLoop_ok`); and, if `big`, the digest for
`core`, the digest's number shifted left by `sh` bits (`prepC_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## `X` -/

theorem min_mask {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b &&&
        (if decide ((BitVec.ofNat 32 a).toNat < (BitVec.ofNat 32 b).toNat) then BitVec.allOnes 32 else 0)) +
      BitVec.ofNat 32 b = BitVec.ofNat 32 (min a b) := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · simp only [h, decide_true, ite_true, BitVec.and_allOnes, BitVec.sub_add_cancel, Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [ite_eq_right_iff.mpr (fun h' => absurd (of_decide_eq_true h') h), Nat.min_eq_right (Nat.le_of_not_lt h)]
    simp

/-- `sub ecx, Q; sbb edx, edx; and ecx, edx; add ecx, Q`: the smaller of
`ecx` and `Q` in `ecx`. -/
theorem min_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (hcx : u.gpr .ecx = BitVec.ofNat 32 a) :
    WP isa (.block [.alu .sub .ecx (.imm (BitVec.ofNat 32 b)), .alu .sbb .edx (.reg .edx),
      .alu .and .ecx (.reg .edx), .alu .add .ecx (.imm (BitVec.ofNat 32 b))]) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .ecx = BitVec.ofNat 32 (min a b) ∧
      ∀ r, r ≠ .ecx → r ≠ .edx → u'.gpr r = u.gpr r := by
  refine wp_subi fun u₁ v₁ hc₁ _ => wp_sbb_self hc₁ fun u₂ v₂ => wp_and fun u₃ v₃ => wp_addi fun u₄ v₄ =>
    WP.block_nil ⟨?_, by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem], ?_, fun r h₁ h₂ => ?_⟩
  · exact hc.regs hL (by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd]) (by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr])
      (by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem])
      (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)])
      (by rw [v₄.syms, v₃.syms, v₂.syms, v₁.syms])
  · rw [v₄.gpr, v₃.gpr, v₂.gpr, v₂.other .ecx (by decide), v₁.gpr, hcx]
    exact min_mask ha hb
  · rw [v₄.other _ h₁, v₃.other _ h₁, v₂.other _ h₂, v₁.other _ h₁]

/-- `ebx = esp + o - ecx`, and the digest in `esi`. -/
theorem xTail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (o : Nat) :
    WP isa (.block [.mov .ebx (.reg .esp), .alu .add .ebx (.imm (BitVec.ofNat 32 o)), .alu .sub .ebx (.reg .ecx),
      .mov .esi (argM 2)]) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
      u'.gpr .ebx = L.F + BitVec.ofNat 32 o - u.gpr .ecx ∧ u'.gpr .esi = L.a2 ∧
      ∀ r, r ≠ .ebx → r ≠ .esi → u'.gpr r = u.gpr r := by
  refine wp_mov fun u₁ v₁ => wp_addi fun u₂ v₂ => wp_sub fun u₃ v₃ _ => ?_
  have c₃ : Ctx L g m₀ u₃ := hc.regs hL (by rw [v₃.rd, v₂.rd, v₁.rd]) (by rw [v₃.wr, v₂.wr, v₁.wr])
    (by rw [v₃.mem, v₂.mem, v₁.mem]) (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)])
    (by rw [v₃.syms, v₂.syms, v₁.syms])
  refine WP.mono (arg_ok hL c₃ (d := .esi) (by decide) (i := 2) (by decide)) fun u₄ h₄ =>
    ⟨h₄.ctx, by rw [h₄.mem, v₃.mem, v₂.mem, v₁.mem], ?_, h₄.val, fun r h₁ h₂ => ?_⟩
  · rw [h₄.keep _ (by decide), v₃.gpr, v₂.gpr, v₂.other .ecx (by decide), v₁.gpr, v₁.other .ecx (by decide),
      hc.esp]
  · rw [h₄.keep _ h₂, v₃.other _ h₁, v₂.other _ h₁, v₁.other _ h₁]

theorem sub_min32 (F : BitVec 32) {a b c : Nat} (h : c ≤ b) :
    F + BitVec.ofNat 32 (a + b) - BitVec.ofNat 32 c = F + BitVec.ofNat 32 (a + (b - c)) := by
  rw [show a + b = a + (b - c) + c by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- The arguments of `X`'s copy: `X` cleared, `ecx = m = min(D, Q)`, the
digest in `esi`, `X + Q - m` in `ebx`. -/
theorem xArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xArgs) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fX)) 72 = List.replicate 72 0 ∧
      u.gpr .ecx = BitVec.ofNat 32 (min P.F.H.D P.Q) ∧
      u.gpr .ebx = L.F + BitVec.ofNat 32 (fX + (P.Q - min P.F.H.D P.Q)) ∧ u.gpr .esi = L.a2 := by
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.xArgs, WP.block_append_iff]
  refine WP.mono (zero18_ok hL (o := fX) (by decide) (by decide) hc) fun u₁ ⟨hc₁, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.mov .ecx (.mem (stk fDl)), .alu .sub .ecx (.imm (BitVec.ofNat 32 P.Q)),
      .alu .sbb .edx (.reg .edx), .alu .and .ecx (.reg .edx), .alu .add .ecx (.imm (BitVec.ofNat 32 P.Q)),
      .mov .ebx (.reg .esp), .alu .add .ebx (.imm (BitVec.ofNat 32 (fX + P.Q))), .alu .sub .ebx (.reg .ecx),
      .mov .esi (argM 2)] : List Instr) =
    [.mov .ecx (.mem (stk fDl))] ++ [.alu .sub .ecx (.imm (BitVec.ofNat 32 P.Q)),
      .alu .sbb .edx (.reg .edx), .alu .and .ecx (.reg .edx), .alu .add .ecx (.imm (BitVec.ofNat 32 P.Q))] ++
      [.mov .ebx (.reg .esp), .alu .add .ebx (.imm (BitVec.ofNat 32 (fX + P.Q))), .alu .sub .ebx (.reg .ecx),
        .mov .esi (argM 2)] from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc₁ (d := .ecx) (by decide) (o := fDl) (by decide)) fun u₂ h₂ => ?_
  have hcx₂ : u₂.gpr .ecx = BitVec.ofNat 32 P.F.H.D := by rw [h₂.val, hc₁.dl hT]
  refine WP.mono (min_ok hL h₂.ctx (a := P.F.H.D) (b := P.Q) (by omega) (by omega) hcx₂)
    fun u₃ ⟨hc₃, hm₃, hcx₃, _⟩ => ?_
  refine WP.mono (xTail_ok hL hc₃ (fX + P.Q)) fun u₄ ⟨hc₄, hm₄, hbx₄, hsi₄, hg₄⟩ => ?_
  have hm : min P.F.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  rw [hcx₃, sub_min32 _ hm] at hbx₄
  have hmm : u₄.mem = u₁.mem := by rw [hm₄, hm₃, h₂.mem]
  exact ⟨hc₄, hmm ▸ hf₁, hmm ▸ hb₁, by rw [hg₄ _ (by decide) (by decide), hcx₃], hbx₄, hsi₄⟩

/-- `X`, the `Q` bytes at `fX`: `Q - m` zero bytes, then the digest's first
`m = min(D, Q)`. -/
theorem prepX_ok (hL : L.Ok) (hT : TabL P L) (hdn : P.F.H.D ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepX t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fX)) P.Q =
        List.replicate (P.Q - min P.F.H.D P.Q) 0 ++ Spec.Sha256.bytesAt t.mem L.dg (min P.F.H.D P.Q) := by
  have hnb := hL.nB
  have ng := hL.ng
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  rw [Cfg.prepX]
  refine WP.seq (WP.mono (xArgs_ok hL hT hc) fun u₅ ⟨hc₅, hf₁, hb₁, hcx₅, hbx₅, hsi₅⟩ => ?_)
  have hm : min P.F.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  have hm8 : 8 ≤ min P.F.H.D P.Q := by omega
  have hdn' : min P.F.H.D P.Q ≤ dn := by omega
  have ea : (L.F + BitVec.ofNat 32 (fX + (P.Q - min P.F.H.D P.Q))).setWidth 64 =
      L.B + BitVec.ofNat 64 (76 + fX + (P.Q - min P.F.H.D P.Q)) := by
    rw [hL.frv (by simp only [fX]; omega), Nat.add_assoc]
  have sepD : Region.Disjoint ⟨L.a2.setWidth 64, min P.F.H.D P.Q⟩
      ⟨L.B + BitVec.ofNat 64 (76 + fX + (P.Q - min P.F.H.D P.Q)), min P.F.H.D P.Q⟩ :=
    ((hL.kg.sub_left (Offset.sub_base _ (by simp only [fX]; omega))).symm.sub_left (Region.sub_prefix hdn'))
  refine WP.mono (cpLoop_ok hL hc₅ (S := L.a2) (D := L.F + BitVec.ofNat 32 (fX + (P.Q - min P.F.H.D P.Q)))
      (n := min P.F.H.D P.Q) (by omega) (by omega) (by omega)
      (by rw [hL.frN (by simp only [fX]; omega)]; have := hL.e28; have := hL.e588; simp only [fX]; omega)
      (by have := hc₅.inDg (o := 0) (n := min P.F.H.D P.Q) (by omega) (by omega); rwa [BitVec.add_zero] at this)
      (by rw [ea]; exact hc₅.inFrW (by omega) (by simp only [fX]; omega) hL)
      (by rw [ea]; exact sepD)
      (by rw [ea]; exact safe_high L (by simp only [fX]; omega) (by simp only [fX]; omega))
      hsi₅ hbx₅ hcx₅) fun u ⟨hc', hf, hb, _⟩ => ?_
  rw [ea] at hf hb
  have hdg : Spec.Sha256.bytesAt u₅.mem L.dg (min P.F.H.D P.Q) = Spec.Sha256.bytesAt t.mem L.dg (min P.F.H.D P.Q) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 76 + fX) (n := 72) (k := 588)
        (by simp only [fX]; omega) a h₂) (Region.sub_prefix hdn' a h₁)) (by omega)
  refine ⟨hc', hf₁.trans ?_, ?_⟩
  · exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by simp only [fX]; omega)⟩
  · rw [show P.Q = (P.Q - min P.F.H.D P.Q) + min P.F.H.D P.Q by omega, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, hb, ← show P.Q = (P.Q - min P.F.H.D P.Q) + min P.F.H.D P.Q by omega,
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega)) (by simp only [fX]; omega) (by simp only [fX]; omega)) (by omega),
      hdg]
    rw [bytesAt_take _ _ (k := 72) (by omega), hb₁, List.take_replicate, Nat.min_eq_left (by omega)]

/-! ## P-521's digest for `core` -/

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- The arguments of the copy of `core`'s digest, if `big`: it cleared,
`ecx = D`, the digest in `esi`, `Xc + Q - 1 - D` in `ebx`. -/
theorem xcArgs_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xcArgs) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + fXc), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fXc)) 72 = List.replicate 72 0 ∧
      u.gpr .ecx = BitVec.ofNat 32 P.F.H.D ∧
      u.gpr .ebx = L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D)) ∧ u.gpr .esi = L.a2 := by
  obtain ⟨-, -, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zero18_ok hL (o := fXc) (by decide) (by decide) hc) fun u₁ ⟨hc₁, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.mov .ecx (.mem (stk fDl)), .mov .ebx (.reg .esp),
      .alu .add .ebx (.imm (BitVec.ofNat 32 (fXc + P.Q - 1))), .alu .sub .ebx (.reg .ecx),
      .mov .esi (argM 2)] : List Instr) =
    [.mov .ecx (.mem (stk fDl))] ++ [.mov .ebx (.reg .esp), .alu .add .ebx (.imm (BitVec.ofNat 32 (fXc + P.Q - 1))),
        .alu .sub .ebx (.reg .ecx), .mov .esi (argM 2)] from rfl, WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc₁ (d := .ecx) (by decide) (o := fDl) (by decide)) fun u₂ h₂ => ?_
  have hcx₂ : u₂.gpr .ecx = BitVec.ofNat 32 P.F.H.D := by rw [h₂.val, hc₁.dl hT]
  refine WP.mono (xTail_ok hL h₂.ctx (fXc + P.Q - 1)) fun u₃ ⟨hc₃, hm₃, hbx₃, hsi₃, hg₃⟩ => ?_
  rw [hcx₂, show fXc + P.Q - 1 = fXc + (P.Q - 1) by simp only [fXc]; omega, sub_min32 _ (by omega),
    show fXc + (P.Q - 1 - P.F.H.D) = fXc + (P.Q - 1 - P.F.H.D) from rfl] at hbx₃
  have hmm : u₃.mem = u₁.mem := by rw [hm₃, h₂.mem]
  exact ⟨hc₃, hmm ▸ hf₁, hmm ▸ hb₁, by rw [hg₃ _ (by decide) (by decide), hcx₂], hbx₃, hsi₃⟩

/-- If `big`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem prepC_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) (hdn : P.F.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepC t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (76 + fXc), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fXc)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.F.H.D) * 2 ^ P.R.sh) := by
  have hnb := hL.nB
  have ng := hL.ng
  obtain ⟨-, -, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hsl := P.R.nBits_len
  have hnb5 := (P.R.sizesW hW).2.2
  have hsh8 : P.R.sh < 8 := by simp only [RfcHash.Q] at hQ66; omega
  have hsh1 : 1 ≤ P.R.sh := by simp only [RfcHash.Q] at hQ66; omega
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.prepC]
  refine WP.seq (WP.mono (xcArgs_ok hL hT hW hc) fun u₁ ⟨hc₁, hf₁, hb₁, hcx₁, hbx₁, hsi₁⟩ => ?_)
  have ea : (L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D))).setWidth 64 =
      L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D)) := by
    rw [hL.frv (by simp only [fXc]; omega), Nat.add_assoc]
  have sepD : Region.Disjoint ⟨L.a2.setWidth 64, P.F.H.D⟩
      ⟨L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D)), P.F.H.D⟩ :=
    ((hL.kg.sub_left (Offset.sub_base _ (by simp only [fXc]; omega))).symm.sub_left (Region.sub_prefix hdn))
  have hdg : Spec.Sha256.bytesAt u₁.mem L.dg P.F.H.D = Spec.Sha256.bytesAt t.mem L.dg P.F.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 76 + fXc) (n := 72) (k := 588)
        (by simp only [fXc]; omega) a h₂) (Region.sub_prefix hdn a h₁)) (by omega)
  refine WP.seq (WP.mono (cpLoop_ok hL hc₁ (S := L.a2) (D := L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D)))
      (n := P.F.H.D) (by omega) (by omega) (by omega)
      (by rw [hL.frN (by simp only [fXc]; omega)]; have := hL.e28; have := hL.e588; simp only [fXc]; omega)
      (by have := hc₁.inDg (o := 0) (n := P.F.H.D) (by omega) (by omega); rwa [BitVec.add_zero] at this)
      (by rw [ea]; exact hc₁.inFrW (by omega) (by simp only [fXc]; omega) hL)
      (by rw [ea]; exact sepD)
      (by rw [ea]; exact safe_high L (by simp only [fXc]; omega) (by simp only [fXc]; omega))
      hsi₁ hbx₁ hcx₁) fun u₄ ⟨hc₄, hf₄, hb₄, _⟩ => ?_)
  rw [ea] at hf₄ hb₄
  refine WP.seq (WP.mono (scrPtr_ok hL hc₄) fun u₅ ⟨hc₅, hm₅, hdi₅, _⟩ => ?_)
  rw [hsc]
  refine WP.mono (conv_ok hL hW hc₅ hdi₅ (o := fXc) (s := 8 - P.R.sh) (by decide) (by decide) (by omega)
    (by omega)) fun u₆ ⟨hc₆, _, hf₆, hb₆⟩ => ?_
  refine ⟨hc₆, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hf₄.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans
      (hm₅ ▸ hf₆.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by simp only [fXc]; omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    have hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (76 + fXc + a)) n =
        List.replicate n 0 := fun a n han => by
      have h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 (76 + fXc)) (n := a + n) (k := 72) (by omega)
      rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
    have hY : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc)) P.Q =
        List.replicate (P.Q - 1 - P.F.H.D) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.F.H.D ++ List.replicate 1 0) := by
      have e := Proof.Hmac.Common.bytesAt_add u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc)) (P.Q - 1 - P.F.H.D)
        (P.F.H.D + 1)
      have e' := Proof.Hmac.Common.bytesAt_add u₄.mem
        (L.B + BitVec.ofNat 64 (76 + fXc) + BitVec.ofNat 64 (P.Q - 1 - P.F.H.D)) P.F.H.D 1
      rw [show P.Q - 1 - P.F.H.D + (P.F.H.D + 1) = P.Q by omega] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      have p₁ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc)) (P.Q - 1 - P.F.H.D) =
          List.replicate (P.Q - 1 - P.F.H.D) 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega)) (by simp only [fXc]; omega) (by simp only [fXc]; omega))
          (by omega)]
        have := hz 0 (P.Q - 1 - P.F.H.D) (by omega)
        rwa [Nat.add_zero] at this
      have p₃ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D) + P.F.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by omega)) (by simp only [fXc]; omega) (by simp only [fXc]; omega))
          (by omega), show 76 + fXc + (P.Q - 1 - P.F.H.D) + P.F.H.D = 76 + fXc + (P.Q - 1 - P.F.H.D + P.F.H.D) by omega]
        exact hz (P.Q - 1 - P.F.H.D + P.F.H.D) 1 (by omega)
      rw [e, e', hb₄, hdg, p₁, p₃]
    rw [hb₆, hm₅, hY, ofBytes_zeros, ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

end VG.Proof.Ecdsa.Rfc6979.X86
