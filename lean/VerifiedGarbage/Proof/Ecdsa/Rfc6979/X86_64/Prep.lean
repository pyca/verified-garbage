module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Wide
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Loops
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on x86-64: the digest into `X`

The byte loop `cpLoop`, `rcx` bytes from `rsi` to `rdi` with `Ctx` kept, for
a destination the code may write apart from the source (`cp_ok`), and `X`
(`prepX_ok`): `Q - m` zero bytes, then the digest's first `m = min(D, Q)`,
its length the smaller of the frame's `D` and `Q` (`min_ok`, by `cmovae`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Impl.Mgf1.X86_64 (ix byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.RsaOaep.X86_64 (StepOk stepR_ok byteLoop_ok ea_ix)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## A byte loop -/

structure CpI (u₀ : State) (p q : Addr) (j : Nat) (v : State) : Prop where
  keep : Keep [.rax, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  mem : ∀ x, v.mem x = if (⟨p, j⟩ : Region).Contains x 1 then u₀.mem (q + (x - p)) else u₀.mem x

theorem cpRaw_ok {u₀ : State} {p q : Addr} {n : Nat} (hs : StepOk (.reg .rcx) n u₀ [.rax, .r8])
    (hn : 0 < n) (hpn : n < 2 ^ 63) (hw : InRegions u₀.wr p n)
    (hsrc : ∀ i < n, InRegions (u₀.rd ++ u₀.wr) (q + BitVec.ofNat 64 i) 1)
    (hd : ∀ i < n, ¬ (⟨p, n⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1)
    (hdi : u₀.gpr .rdi = p) (hsi : u₀.gpr .rsi = q) (h8 : u₀.gpr .r8 = BitVec.ofNat 64 0) :
    WP isa Cfg.cpLoop u₀ fun u' =>
      Keep [.rax, .r8] u₀ u' ∧
      ∀ x, u'.mem x = if (⟨p, n⟩ : Region).Contains x 1 then u₀.mem (q + (x - p)) else u₀.mem x := by
  refine WP.mono (byteLoop_ok hn hs (CpI u₀ p q) ?_ (u := u₀)
    ⟨Keep.refl _ _, h8, fun x => by simp [Region.Contains]⟩) fun u' I => ⟨I.keep, I.mem⟩
  intro j hj v I
  have hdv : v.gpr .rdi = p := (I.keep.gpr (by decide)).trans hdi
  have hsv : v.gpr .rsi = q := (I.keep.gpr (by decide)).trans hsi
  have hea : ∀ b : Addr, b + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = b + BitVec.ofNat 64 j := fun b => by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have hin : InRegions v.wr (p + BitVec.ofNat 64 j) 1 := by
    obtain ⟨R, hR, hc⟩ := hw
    refine ⟨R, I.keep.2.2 ▸ hR, hc.byte ?_⟩
    rw [BitVec.add_comm p, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hj
  have hrd : InRegions (v.rd ++ v.wr) (q + BitVec.ofNat 64 j) 1 := by
    rw [I.keep.2.1, I.keep.2.2]; exact hsrc j hj
  have hq : v.mem (q + BitVec.ofNat 64 j) = u₀.mem (q + BitVec.ofNat 64 j) := by
    rw [I.mem, ifn]
    exact fun h => hd j hj (by
      simp only [Region.Contains] at h ⊢; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (p + BitVec.ofNat 64 j) (u₀.mem (q + BitVec.ofNat 64 j))) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [Cfg.cpBody, ea_ix, hdv, hsv, I.r8, hea, hin, hrd, hq]
    simp
  refine ⟨(I.keep.trans (k.trans k')).mono (by decide), h8'', fun x => ?_⟩
  rw [hm', hm, VG.WriteBytes.writeW8_apply, I.mem x]
  by_cases he : x = p + BitVec.ofNat 64 j
  · subst he
    rw [ifp rfl, ifp (show (⟨p, j + 1⟩ : Region).Contains (p + BitVec.ofNat 64 j) 1 from
      Offset.contains_base _ (by omega) (by omega))]
    congr 1
    rw [BitVec.add_comm p, BitVec.add_sub_cancel]
  · rw [ifn he]
    have hne : (x - p).toNat ≠ j := fun h => he (by
      rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
    have iff : (⟨p, j + 1⟩ : Region).Contains x 1 ↔ (⟨p, j⟩ : Region).Contains x 1 := by
      simp only [Region.Contains]; omega
    by_cases h1 : (⟨p, j⟩ : Region).Contains x 1
    · rw [ifp h1, ifp (iff.mpr h1)]
    · rw [ifn h1, ifn (fun h => h1 (iff.mp h))]

/-- `n` bytes from `q` (`rsi`) to `p` (`rdi`), `n` in `rcx`, by `cpLoop`:
`Ctx` kept, for a destination the code may write apart from the source. -/
theorem cp_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {p q : Addr} {n : Nat} (hn : 0 < n)
    (hn' : n < 2 ^ 63) (hcx : u.gpr .rcx = BitVec.ofNat 64 n) (hdi : u.gpr .rdi = p) (hsi : u.gpr .rsi = q)
    (h8 : u.gpr .r8 = BitVec.ofNat 64 0) (hpn : p.toNat + n ≤ 2 ^ 64) (hw : InRegions u.wr p n)
    (hs : Safe L ⟨p, n⟩) (hsrc : ∀ i < n, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 i) 1)
    (hd : ∀ i < n, ¬ (⟨p, n⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    WP isa Cfg.cpLoop u fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .rax → r ≠ .r8 → u'.gpr r = u.gpr r) ∧
      Frame [⟨p, n⟩] u.mem u'.mem ∧ Spec.Sha256.bytesAt u'.mem p n = Spec.Sha256.bytesAt u.mem q n := by
  refine WP.mono_syms (cpRaw_ok (stepR_ok hn' u (by decide) (by decide) hcx) hn hn' hw hsrc hd hdi hsi h8)
    fun u' ⟨hk, hm⟩ hsy => ?_
  have hg : ∀ r, r ≠ .rax → r ≠ .r8 → u'.gpr r = u.gpr r := fun r h₁ h₂ =>
    hk.gpr (by simp [h₁, h₂])
  have hf : Frame [⟨p, n⟩] u.mem u'.mem := fun x hx => by
    rw [hm x, ifn (hx _ (List.mem_singleton_self _))]
  refine ⟨hc.keep hL hk.2.1 hk.2.2 (hg _ (by decide) (by decide))
      (fun r hr _ => hg r (ne_cs hr (by decide)) (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs) hsy, hg, hf, ?_⟩
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [hm, ifp (Offset.contains_base _ (d := i) (by omega) (by omega)), BitVec.add_comm p, BitVec.add_sub_cancel]

/-! ## `X` -/

/-- `cmp rcx, rax; cmovae rcx, rax`: the smaller of the two in `rcx`. -/
theorem min_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hcx : u.gpr .rcx = BitVec.ofNat 64 a) (hax : u.gpr .rax = BitVec.ofNat 64 b) :
    WP isa (.block [.alu .cmp .rcx (.reg .rax), .cmov .ae .rcx (.reg .rax)]) u
      (Upd L g m₀ u .rcx (BitVec.ofNat 64 (min a b))) := by
  apply WP.of_runBlock
  have hta : (u.gpr .rcx).toNat = a := by rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have htb : (u.gpr .rax).toNat = b := by rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, hta, htb, h,
      RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, Option.bind_some, Option.map_some, decide_true, ↓reduceIte,
      Bool.not_true, Bool.false_eq_true, Option.some.injEq, exists_eq_left']
    exact ⟨hc.set hL (d := .rcx) (by decide) rfl rfl rfl rfl fun r _ => by rw [RegUpd.gpr_arithFlags], rfl,
      by rw [RegUpd.gpr_arithFlags, hcx, Nat.min_eq_left (by omega)], fun r _ => by rw [RegUpd.gpr_arithFlags]⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, hta, htb, h,
      RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, Option.bind_some, Option.map_some, decide_false, ↓reduceIte,
      Bool.not_false, Option.some.injEq, exists_eq_left']
    exact ⟨hc.set hL (d := .rcx) (by decide) rfl rfl rfl rfl fun r hr => by
        rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags], rfl,
      by rw [RegUpd.gpr_setReg_self, hax, Nat.min_eq_right (by omega)],
      fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]⟩

/-- `rdi = rsp + o - rcx`, the digest in `rsi` and `r8 = 0`. -/
theorem xTail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho : o < 2 ^ 31) :
    WP isa (.block [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 o)), .alu .sub .rdi (.reg .rcx),
      .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)]) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
      u'.gpr .rdi = L.B + BitVec.ofNat 64 (24 + o) - u.gpr .rcx ∧ u'.gpr .rsi = L.dg ∧
      u'.gpr .r8 = BitVec.ofNat 64 0 ∧ ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → u'.gpr r = u.gpr r := by
  have h216 := hc.inFr (d := 216) (by decide) (by have := L.he; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execAlu32, readSrc, readSrc32,
    State.setReg32, State.load64, ea_stk, hc.rsp, sx32 ho, Offset.add_add, fDigest, Nat.reduceAdd, h216, ite_true, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, reduceCtorEq, ite_false,
    hc.pDg, xor_self_zx, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, rfl,
    fun r h₁ h₂ h₃ => by simp only [h₁, h₂, h₃, ite_false]⟩

theorem sub_min (B : Addr) {a b c : Nat} (h : c ≤ b) :
    B + BitVec.ofNat 64 (a + b) - BitVec.ofNat 64 c = B + BitVec.ofNat 64 (a + (b - c)) := by
  rw [show a + b = a + (b - c) + c by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- `X`, the `Q` bytes at `fX`: `Q - m` zero bytes, then the digest's first
`m = min(D, Q)`. -/
theorem prepX_ok (hL : L.Ok) (hT : TabL P L) (hdn : P.H.D ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepX t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fX)) P.Q =
        List.replicate (P.Q - min P.H.D P.Q) 0 ++ Spec.Sha256.bytesAt t.mem L.dg (min P.H.D P.Q) := by
  have he := L.he
  have hnb := hL.nb
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.prepX]
  refine WP.seq ?_
  rw [Cfg.xArgs, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fX) (by decide) (by simp only [fX]; omega) 9 (Nat.le_refl _) hc)
    fun u₁ ⟨hc₁, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.mov .rcx (.mem (stk fDl)), .mov32 .rax (.imm (BitVec.ofNat 32 P.Q)), .alu .cmp .rcx (.reg .rax),
      .cmov .ae .rcx (.reg .rax), .mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 (fX + P.Q))),
      .alu .sub .rdi (.reg .rcx), .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] : List Instr) =
    [.mov .rcx (.mem (stk fDl))] ++ [.mov32 .rax (.imm (BitVec.ofNat 32 P.Q))] ++
      [.alu .cmp .rcx (.reg .rax), .cmov .ae .rcx (.reg .rax)] ++
      [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 (fX + P.Q))),
        .alu .sub .rdi (.reg .rcx), .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc₁ (d := .rcx) (by decide) (o := fDl) (by simp only [fDl]; omega)) fun u₂ h₂ => ?_
  refine WP.mono (mov32_ok hL h₂.ctx (d := .rax) (by decide) (n := P.Q) (by omega)) fun u₃ h₃ => ?_
  have hcx₃ : u₃.gpr .rcx = BitVec.ofNat 64 P.H.D := by
    rw [h₃.keep _ (by decide), h₂.val, hc₁.dl hT]
  refine WP.mono (min_ok hL h₃.ctx (a := P.H.D) (b := P.Q) (by omega) (by omega) hcx₃ h₃.val) fun u₄ h₄ => ?_
  refine WP.mono (xTail_ok hL h₄.ctx (o := fX + P.Q) (by simp only [fX]; omega))
    fun u₅ ⟨hc₅, hm₅, hdi₅, hsi₅, h8₅, hg₅⟩ => ?_
  have hm : min P.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  have hm8 : 8 ≤ min P.H.D P.Q := by omega
  have hx : 24 + fX + (P.Q - min P.H.D P.Q) + min P.H.D P.Q = 24 + fX + P.Q := by omega
  rw [h₄.val, ← Nat.add_assoc, sub_min _ hm] at hdi₅
  refine WP.mono (cp_ok hL hc₅ (p := L.B + BitVec.ofNat 64 (24 + fX + (P.Q - min P.H.D P.Q))) (q := L.dg)
      (n := min P.H.D P.Q) (by omega) (by omega) (by rw [hg₅ _ (by decide) (by decide) (by decide), h₄.val])
      hdi₅ hsi₅ h8₅ ?_ (hc₅.inFrW (by omega) (by simp only [fX]; omega))
      (safe_high L (by simp only [fX]; omega) (by simp only [fX]; omega))
      (fun i hi => hc₅.inDg (o := i) (n := 1) (by omega) (by omega))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 248 + 8 * L.e) (by simp only [fX]; omega) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := dn) (by omega) (by omega))))
    fun u ⟨hc', _, hf, hb⟩ => ?_
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 + fX + _) (by simp only [fX]; omega),
      Nat.mod_eq_of_lt (by simp only [fX]; omega)]
    simp only [fX]; omega
  have hm₄ : u₅.mem = u₁.mem := by rw [hm₅, h₄.mem, h₃.mem, h₂.mem]
  have hdn' : min P.H.D P.Q ≤ dn := by omega
  have hdg : Spec.Sha256.bytesAt u₁.mem L.dg (min P.H.D P.Q) = Spec.Sha256.bytesAt t.mem L.dg (min P.H.D P.Q) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 24 + fX) (n := 72) (k := 248 + 8 * L.e)
        (by simp only [fX]; omega) a h₂) (Region.sub_prefix hdn' a h₁)) (by omega)
  refine ⟨hc', hf₁.trans ?_, ?_⟩
  · rw [← hm₄]
    exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by simp only [fX]; omega)⟩
  · rw [show P.Q = (P.Q - min P.H.D P.Q) + min P.H.D P.Q by omega, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, hb, ← show P.Q = (P.Q - min P.H.D P.Q) + min P.H.D P.Q by omega,
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega)) (by simp only [fX]; omega) (by simp only [fX]; omega)) (by omega),
      hm₅, h₄.mem, h₃.mem, h₂.mem, hdg]
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
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + fXc), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fXc)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.H.D) * 2 ^ P.R.sh) := by
  have he := L.he
  have hnb := hL.nb
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
  refine WP.mono (zero9_ok hL (o := fXc) (by decide) (by simp only [fXc]; omega) 9 (Nat.le_refl _) hc)
    fun u₁ ⟨hc₁, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.mov .rcx (.mem (stk fDl)), .mov .rdi (.reg .rsp),
      .alu .add .rdi (.imm (BitVec.ofNat 32 (fXc + P.Q - 1))), .alu .sub .rdi (.reg .rcx),
      .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] : List Instr) =
    [.mov .rcx (.mem (stk fDl))] ++
      [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 (fXc + P.Q - 1))),
        .alu .sub .rdi (.reg .rcx), .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] from rfl,
    WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc₁ (d := .rcx) (by decide) (o := fDl) (by simp only [fDl]; omega)) fun u₂ h₂ => ?_
  have hcx₂ : u₂.gpr .rcx = BitVec.ofNat 64 P.H.D := by rw [h₂.val, hc₁.dl hT]
  refine WP.mono (xTail_ok hL h₂.ctx (o := fXc + P.Q - 1) (by simp only [fXc]; omega))
    fun u₃ ⟨hc₃, hm₃, hdi₃, hsi₃, h8₃, hg₃⟩ => ?_
  have hx : 24 + (fXc + P.Q - 1 - P.H.D) = 24 + fXc + (P.Q - 1 - P.H.D) := by omega
  rw [hcx₂, sub_min _ (by omega), hx] at hdi₃
  have hm₁ : u₃.mem = u₁.mem := by rw [hm₃, h₂.mem]
  have hdg : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 24 + fXc) (n := 72) (k := 248 + 8 * L.e)
        (by simp only [fXc]; omega) a h₂) (Region.sub_prefix hdn a h₁)) (by omega)
  refine WP.seq (WP.mono (cp_ok hL hc₃ (p := L.B + BitVec.ofNat 64 (24 + fXc + (P.Q - 1 - P.H.D))) (q := L.dg)
      (n := P.H.D) (by omega) (by omega) (by rw [hg₃ _ (by decide) (by decide) (by decide), hcx₂])
      hdi₃ hsi₃ h8₃ ?_ (hc₃.inFrW (by omega) (by simp only [fXc]; omega))
      (safe_high L (by simp only [fXc]; omega) (by simp only [fXc]; omega))
      (fun i hi => hc₃.inDg (o := i) (n := 1) (by omega) (by omega))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 248 + 8 * L.e) (by simp only [fXc]; omega) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := dn) (by omega) (by omega))))
    fun u₄ ⟨hc₄, _, hf₄, hb₄⟩ => ?_)
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 + fXc + _) (by simp only [fXc]; omega),
      Nat.mod_eq_of_lt (by simp only [fXc]; omega)]
    simp only [fXc]; omega
  rw [hsc, WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hc₄) fun u₅ ⟨hc₅, hm₅, hdi₅, _⟩ => ?_
  refine WP.mono (conv_ok hL hW hc₅ hdi₅ (o := fXc) (s := 8 - P.R.sh) (by decide) (by decide) (by omega)
    (by omega)) fun u₆ ⟨hc₆, _, hf₆, hb₆⟩ => ?_
  refine ⟨hc₆, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hm₁ ▸ hf₄.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans
      (hm₅ ▸ hf₆.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by simp only [fXc]; omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    have hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (24 + fXc + a)) n =
        List.replicate n 0 := fun a n han => by
      have h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 (24 + fXc)) (n := a + n) (k := 8 * 9) (by omega)
      rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
    have hY : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (24 + fXc)) P.Q =
        List.replicate (P.Q - 1 - P.H.D) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.H.D ++ List.replicate 1 0) := by
      have e := Proof.Hmac.Common.bytesAt_add u₄.mem (L.B + BitVec.ofNat 64 (24 + fXc)) (P.Q - 1 - P.H.D)
        (P.H.D + 1)
      have e' := Proof.Hmac.Common.bytesAt_add u₄.mem
        (L.B + BitVec.ofNat 64 (24 + fXc) + BitVec.ofNat 64 (P.Q - 1 - P.H.D)) P.H.D 1
      rw [show P.Q - 1 - P.H.D + (P.H.D + 1) = P.Q by omega] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      have p₁ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (24 + fXc)) (P.Q - 1 - P.H.D) =
          List.replicate (P.Q - 1 - P.H.D) 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega)) (by simp only [fXc]; omega) (by simp only [fXc]; omega))
          (by omega), hm₁]
        have := hz 0 (P.Q - 1 - P.H.D) (by omega)
        rwa [Nat.add_zero] at this
      have p₃ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (24 + fXc + (P.Q - 1 - P.H.D) + P.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by omega)) (by simp only [fXc]; omega) (by simp only [fXc]; omega))
          (by omega), hm₁, show 24 + fXc + (P.Q - 1 - P.H.D) + P.H.D = 24 + fXc + (P.Q - 1 - P.H.D + P.H.D) by omega]
        exact hz (P.Q - 1 - P.H.D + P.H.D) 1 (by omega)
      rw [e, e', hb₄, hm₁, hdg, p₁, p₃]
    rw [hb₆, hm₅, hY, ofBytes_zeros, ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

end VG.Proof.Ecdsa.Rfc6979.X86_64
