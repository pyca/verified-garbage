module

public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Frame
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Frame
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# `vg_rsa_pkcs1_recover_precomputed` on RISC-V: correctness

After the call (`AfterCall`), the status is kept in the frame and `encode`
writes to `EM₂` the encoding of the last `out_len` bytes of `EM₁`. If that
fails, `out` is zeroed and the result is 0; if not, those bytes are copied
to `out`, and `out` and the result are masked with whether the encoding is
`EM₁` and the call succeeded (`afterPub_ok`): if `pre` holds the modulus'
values, recovery by encoding (`Proof.RsaPkcs1Sig.recover_eq_recoverEnc`).
As on PPC64LE (`Proof/RsaPkcs1Sig/PPC64LE/RecoverCorrect.lean`).
-/

@[expose] public section

/-!
# `vg_rsa_pkcs1_recover_precomputed` on RISC-V: the call

As `vg_rsa_pkcs1_verify_precomputed`'s (`VerifyCall.lean`): `pubArgs_ok`, the
block before the call, keeps `out`, `out_len`, `k` and `hash` (zero-extended)
in `s1`–`s4` and sets up the call of `vg_rsa_public_precomputed_checked`
(`AtCall`); `call_ok`, the call writes RSAVP1's result to `EM₁` if `pre`
holds the modulus' values (`AfterCall`).
-/


/-!
# `vg_rsa_pkcs1_recover_precomputed` on RISC-V: the precondition

Untrusted: everything here is checked by Lean. `PreR s`: the shared
contract's precondition (`recoverPrecomputedContract`, with the stack of the
frame, `frameBytes`), by name (`preR_of`). As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/RecoverPre.lean`).
-/


namespace VG.Proof.RsaPkcs1Sig.RISCV64.Rec

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

/-- The buffers: `out`, `n`, `e`, the signature and the precomputed values
(the working space, the arguments on the stack and the stack the function
uses are `sR`, `aR` and `kR`). -/
abbrev oR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
abbrev gR (s : State) : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

/-- What the code needs of `recoverPrecomputedContract.pre`, by name. -/
structure PreR (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 40 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, gR s, pR s, aR s]
  hwr : s.wr = [oR s, sR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  og : (oR s).Disjoint (gR s)
  os : (oR s).Disjoint (sR s)
  op : (oR s).Disjoint (pR s)
  oa : (oR s).Disjoint (aR s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  gs : (gR s).Disjoint (sR s)
  sp : (sR s).Disjoint (pR s)
  sa : (sR s).Disjoint (aR s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kg : (kR s).Disjoint (gR s)
  ks : (kR s).Disjoint (sR s)
  kp : (kR s).Disjoint (pR s)
  ka : (kR s).Disjoint (aR s)
  wo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wn : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  we : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  wg : (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  ws : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a3).toNat
  k2 : (s.gpr .a3).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .a5).toNat
  e2 : (s.gpr .a5).toNat ≤ (s.gpr .a3).toNat
  hh : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .a6).setWidth 32).toNat = some h ∧ (s.gpr .a1).toNat = h.len
  hs : Spec.Rsa.publicScratchWords (s.gpr .a3).toNat ≤ (stackArg s 2).toNat
  hp : (stackArg s 4).toNat = Spec.Rsa.precomputedWords (s.gpr .a3).toNat
  al1 : (stackArg s 1).toNat % 8 = 0
  al3 : (stackArg s 3).toNat % 8 = 0

theorem preR_of {s : State} (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes).pre s) : PreR s := by
  have e : frameBytes = 2127 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨spal, sp1, sp2, hrd, hwr, on, oe, og, os, op, oa, ns, es, gs, sp, sa, ko, kn, ke, kg, ks, kp, ka, wo, wn,
    we, wg, ws, wp, ⟨k1, k2⟩, e1, e2, hh, hs, hp, al1, al3⟩ := h
  exact ⟨spal, sp1, sp2, hrd, hwr, on, oe, og, os, op, oa, ns, es, gs, sp, sa, ko, kn, ke, kg, ks, kp, ka, wo, wn,
    we, wg, ws, wp, k1, k2, e1, e2, hh, hs, hp, al1, al3⟩

/-- The hash's length, at least one octet. -/
theorem PreR.len_pos {s : State} (hp : PreR s) : 1 ≤ (s.gpr .a1).toNat := by
  obtain ⟨h, -, e⟩ := hp.hh
  rw [e]; cases h <;> decide

/-- The hash's length, at most 64 octets. -/
theorem PreR.len_le {s : State} (hp : PreR s) : (s.gpr .a1).toNat ≤ 64 := by
  obtain ⟨h, -, e⟩ := hp.hh
  rw [e]; cases h <;> decide

end VG.Proof.RsaPkcs1Sig.RISCV64.Rec


namespace VG.Proof.RsaPkcs1Sig.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64

namespace Rec

open VG.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed

/-- In the frame, `out`, `out_len`, `k` and `hash` kept. -/
abbrev RMid (s t : State) : Prop :=
  Mid (sR s) s (s.gpr .a0) (s.gpr .a1) (s.gpr .a3) (zx (s.gpr .a6)) t

/-- At the call: the arguments of `vg_rsa_public_precomputed_checked`, `EM₁`,
`n_len`, `pre`, `pre_len`, `e`, `e_len`, `sig` and `n_len`, and on the stack
`scratch` and `scratch_len`. -/
structure AtCall (s t : State) : Prop extends
    Mid (sR s) s (s.gpr .a0) (s.gpr .a1) (s.gpr .a3) (zx (s.gpr .a6)) t where
  g0 : t.gpr .a0 = fb s + BitVec.ofNat 64 oEM1
  g1 : t.gpr .a1 = s.gpr .a3
  g2 : t.gpr .a2 = stackArg s 3
  g3 : t.gpr .a3 = stackArg s 4
  g4 : t.gpr .a4 = s.gpr .a4
  g5 : t.gpr .a5 = s.gpr .a5
  g6 : t.gpr .a6 = s.gpr .a7
  g7 : t.gpr .a7 = s.gpr .a3
  sa0 : stackArg t 0 = stackArg s 1
  sa1 : stackArg t 1 = stackArg s 2

section
variable {s : State}

/-- The stack arguments are readable. -/
theorem arg_rd (hp : PreR s) (rs : List Region) {j : Nat} (hj : j < 5) :
    InRegions (s.rd ++ rs) (stackArgAddr s j) 8 :=
  ⟨aR s, List.mem_append_left _ (by rw [hp.hrd]; simp), in_aR hj⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame (hp : PreR s) {m : Mem} (h : Frame [kR s] s.mem m) {j : Nat} (hj : j < 5) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (in_aR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ka.symm) (by decide)

end

theorem pubArgs_ok {s u : State} (hp : PreR s) (hsp : u.sp = fb s) (hwr : u.wr = kR s :: s.wr)
    (hrd : u.rd = s.rd) (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r, r ∉ [Reg.t0] → u.gpr r = s.gpr r) :
    WP isa (.block pubArgs) u (AtCall s) := by
  have hfa := fb_al hp.spal hp.sp1
  unfold pubArgs
  simp only [List.append_assoc]
  refine save_ok hsp hwr (by omega) hm (fun r hr => hg r (by revert r; decide)) fun v kv v0 fv sv => ?_
  have gv : ∀ r, r ∉ [Reg.t0] → v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r hr, hg r hr]
  simp only [zext, List.cons_append, List.nil_append]
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_sll fun v₄ o₄ e₄ =>
    wp_srl fun v₅ o₅ e₅ => wp_mov fun v₆ o₆ e₆ => wp_mov fun v₉ o₇ e₇ => ?_
  have O₉ : Only [.s1, .s2, .s3, .s4, .s4, .a6, .a7] v v₉ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
  have t0₉ : v₉.gpr .t0 = fb s := by rw [O₉.get .t0, v0]
  have rd₉ : v₉.rd = s.rd := by rw [O₉.rd, kv.rd, hrd]
  have wr₉ : v₉.wr = kR s :: s.wr := by rw [O₉.wr, kv.wr, hwr]
  have sp₉ : v₉.sp = fb s := by rw [O₉.sp, kv.sp, hsp]
  unfold callTail argBase
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun w₁ p₁ f₁ => wp_addi fun w₂ p₂ f₂ => ?_
  have t6₂ : w₂.gpr .t6 = stackArgAddr s 0 := by
    rw [f₂, f₁, sp₉, stackArgAddr_fb, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
  have P₂ : Only [.t6, .t6] v₉ w₂ := p₁.trans p₂
  refine wp_ld (a := stackArgAddr s 1) (by rw [t6₂, stackArgAddr_eq s 1]) (arg_al hp.spal 1)
    (by rw [P₂.rd, rd₉]; exact arg_rd hp _ (by decide)) fun v₁₀ o₁₀ e₁₀ => ?_
  rw [P₂.mem, O₉.mem, arg_frame hp fv (by decide)] at e₁₀
  refine wp_sd (a := fb s + BitVec.ofNat 64 0) (by rw [o₁₀.get .t0, P₂.get .t0, t0₉])
    (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁₀.wr, P₂.wr, wr₉]; exact in_fr s _ (by decide)) fun v₁₁ m₁₁ => ?_
  have f₁₁ : Frame [⟨fb s + BitVec.ofNat 64 0, 16⟩] v.mem v₁₁.mem := by
    rw [m₁₁.mem, o₁₀.mem, P₂.mem, O₉.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 0) (e := 0) (by decide) (by decide) (by decide))
  have K₁₁ : Frame [kR s] s.mem v₁₁.mem := fv.trans (f₁₁.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, frame_sub s (by decide)⟩)
  have g₁₁ : ∀ r, r ∉ [Reg.t1] → v₁₁.gpr r = w₂.gpr r := fun r hr => by rw [m₁₁.gpr, o₁₀.gpr r hr]
  have rd₁₁ : v₁₁.rd = s.rd := by rw [m₁₁.rd, o₁₀.rd, P₂.rd, rd₉]
  have wr₁₁ : v₁₁.wr = kR s :: s.wr := by rw [m₁₁.wr, o₁₀.wr, P₂.wr, wr₉]
  refine wp_ld (a := stackArgAddr s 2) (by rw [g₁₁ .t6 (by decide), t6₂, stackArgAddr_eq s 2])
    (arg_al hp.spal 2) (by rw [rd₁₁]; exact arg_rd hp _ (by decide)) fun v₁₂ o₁₂ e₁₂ => ?_
  rw [arg_frame hp K₁₁ (by decide)] at e₁₂
  refine wp_sd (a := fb s + BitVec.ofNat 64 8) (by rw [o₁₂.get .t0, g₁₁ .t0 (by decide), P₂.get .t0, t0₉])
    (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁₂.wr, wr₁₁]; exact in_fr s _ (by decide)) fun v₁₃ m₁₃ => ?_
  have f₁₃ : Frame [⟨fb s + BitVec.ofNat 64 0, 16⟩] v.mem v₁₃.mem := by
    rw [m₁₃.mem, o₁₂.mem]
    exact f₁₁.writeW (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 8) (e := 0) (by decide) (by decide) (by decide))
  have K₁₃ : Frame [kR s] s.mem v₁₃.mem := fv.trans (f₁₃.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, frame_sub s (by decide)⟩)
  have g₁₃ : ∀ r, r ∉ [Reg.t1] → v₁₃.gpr r = w₂.gpr r := fun r hr => by
    rw [m₁₃.gpr, o₁₂.gpr r hr, g₁₁ r hr]
  have rd₁₃ : v₁₃.rd = s.rd := by rw [m₁₃.rd, o₁₂.rd, rd₁₁]
  refine wp_ld (a := stackArgAddr s 3) (by rw [g₁₃ .t6 (by decide), t6₂, stackArgAddr_eq s 3])
    (arg_al hp.spal 3) (by rw [rd₁₃]; exact arg_rd hp _ (by decide)) fun v₁₄ o₁₄ e₁₄ => ?_
  refine wp_ld (a := stackArgAddr s 4) (by rw [o₁₄.get .t6, g₁₃ .t6 (by decide), t6₂, stackArgAddr_eq s 4])
    (arg_al hp.spal 4) (by rw [o₁₄.rd, rd₁₃]; exact arg_rd hp _ (by decide)) fun v₁₅ o₁₅ e₁₅ => ?_
  refine wp_addi fun v₁₆ o₁₆ e₁₆ => wp_mov fun v₁₇ o₁₇ e₁₇ => wp_nil ?_
  rw [arg_frame hp K₁₃ (by decide)] at e₁₄
  rw [o₁₄.mem, arg_frame hp K₁₃ (by decide)] at e₁₅
  have O₁₇ : Only [.a2, .a3, .a0, .a1] v₁₃ v₁₇ := (o₁₄.trans (o₁₅.trans (o₁₆.trans o₁₇))).mono
  have g₁₇ : ∀ r, r ∉ [Reg.a2, .a3, .a0, .a1, .t1, .t6, .t6] → v₁₇.gpr r = v₉.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [O₁₇.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), g₁₃ r (by simp [hr.2.2.2.2.1]),
      P₂.gpr r (by simp [hr.2.2.2.2.2.1])]
  have mem₁₇ : v₁₇.mem = v₁₃.mem := O₁₇.mem
  have hd : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 0, 16⟩ : Region)], ∀ {e k : Nat}, 16 ≤ e → e + k ≤ frameBytes →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 e, k⟩ r := fun r hr e k h₁ h₂ => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega)) (by unfold frameBytes at h₂; omega) (by decide)
  have t0₁₃ : v₁₃.gpr .t0 = fb s := by rw [g₁₃ .t0 (by decide), P₂.get .t0, t0₉]
  refine {
    sp := by rw [O₁₇.sp, m₁₃.sp, o₁₂.sp, m₁₁.sp, o₁₀.sp, P₂.sp, sp₉]
    rd := by rw [O₁₇.rd, rd₁₃]
    wr := by rw [O₁₇.wr, m₁₃.wr, o₁₂.wr, wr₁₁]
    s1 := by
      rw [g₁₇ .s1 (by decide), o₇.get .s1, o₆.get .s1, o₅.get .s1, o₄.get .s1, o₃.get .s1, o₂.get .s1, e₁,
        gv .a0 (by decide)]
    s2 := by
      rw [g₁₇ .s2 (by decide), o₇.get .s2, o₆.get .s2, o₅.get .s2, o₄.get .s2, o₃.get .s2, e₂, o₁.get .a1,
        gv .a1 (by decide)]
    s3 := by
      rw [g₁₇ .s3 (by decide), o₇.get .s3, o₆.get .s3, o₅.get .s3, o₄.get .s3, e₃, o₂.get .a3, o₁.get .a3,
        gv .a3 (by decide)]
    s4 := by
      rw [g₁₇ .s4 (by decide), o₇.get .s4, o₆.get .s4, e₅, e₄, o₃.get .a6, o₂.get .a6, o₁.get .a6,
        gv .a6 (by decide), zext_eq]
    hi := fun r hr => by
      have h₁ : r ∉ [Reg.a2, .a3, .a0, .a1, .t1, .t6, .t6] := by revert r; decide
      have h₃ : r ∉ [Reg.s1, .s2, .s3, .s4, .s4, .a6, .a7] := by revert r; decide
      have h₄ : r ∉ [Reg.t0] := by revert r; decide
      rw [g₁₇ r h₁, O₉.gpr r h₃, gv r h₄]
    mem := by
      rw [mem₁₇]
      exact K₁₃.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
    sv := by
      rw [mem₁₇]
      exact sv.frame_in saved_offs f₁₃ fun r hr => hd r hr (by decide) (by decide)
    g0 := by rw [o₁₇.get .a0, e₁₆, o₁₅.get .t0, o₁₄.get .t0, t0₁₃]
    g1 := by rw [e₁₇, o₁₆.get .s3, o₁₅.get .s3, o₁₄.get .s3, g₁₃ .s3 (by decide), P₂.get .s3,
      o₇.get .s3, o₆.get .s3, o₅.get .s3, o₄.get .s3, e₃, o₂.get .a3, o₁.get .a3, gv .a3 (by decide)]
    g2 := by rw [o₁₇.get .a2, o₁₆.get .a2, o₁₅.get .a2, e₁₄]
    g3 := by rw [o₁₇.get .a3, o₁₆.get .a3, e₁₅]
    g4 := by rw [g₁₇ .a4 (by decide), O₉.get .a4, gv .a4 (by decide)]
    g5 := by rw [g₁₇ .a5 (by decide), O₉.get .a5, gv .a5 (by decide)]
    g6 := by
      rw [g₁₇ .a6 (by decide), o₇.get .a6, e₆, o₅.get .a7, o₄.get .a7, o₃.get .a7, o₂.get .a7, o₁.get .a7,
        gv .a7 (by decide)]
    g7 := by
      rw [g₁₇ .a7 (by decide), e₇, o₆.get .a3, o₅.get .a3, o₄.get .a3, o₃.get .a3, o₂.get .a3, o₁.get .a3,
        gv .a3 (by decide)]
    sa0 := by
      show v₁₇.mem.readW (v₁₇.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
      rw [O₁₇.sp, m₁₃.sp, o₁₂.sp, m₁₁.sp, o₁₀.sp, P₂.sp, sp₉, mem₁₇, m₁₃.mem, o₁₂.mem,
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), m₁₁.mem,
        Mem.readW_writeW_self64]
      exact e₁₀
    sa1 := by
      show v₁₇.mem.readW (v₁₇.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
      rw [O₁₇.sp, m₁₃.sp, o₁₂.sp, m₁₁.sp, o₁₀.sp, P₂.sp, sp₉, mem₁₇, m₁₃.mem, Mem.readW_writeW_self64]
      exact e₁₂ }

/-- The values of the modulus `pre` holds, which the result is about. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat)

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (s.gpr .a3).toNat)

/-- `EM₁`, of `k` bytes. -/
abbrev em1R (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .a3).toNat⟩

theorem em1_sub {s : State} (hp : PreR s) : Region.Sub (em1R s) (kR s) :=
  frame_sub s (by have := hp.k2; unfold oEM1 frameBytes; omega)

theorem pdOk_of {s t : State} (hp : PreR s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .a3) : PdOk t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp.sp1
  have hfa := fb_al hp.spal hp.sp1
  have hgK : (kR s).Disjoint ⟨s.gpr .a7, (s.gpr .a3).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .a7, (s.gpr .a3).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  have hsa : stackArgAddr t 0 = fb s + BitVec.ofNat 64 0 := by rw [stackArgAddr, ha.sp]
  refine ⟨?hl, ?spal, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs, ?al2, ?al0⟩
  case hl =>
    rw [ha.g0, ha.g1, ha.g2, ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.sa0, ha.sa1, hsa]
    exact {
      on := hp.kp.sub_left (em1_sub hp)
      oe := hp.ke.sub_left (em1_sub hp)
      oi := hgK.sub_left (em1_sub hp)
      os := hp.ks.sub_left (em1_sub hp)
      oa := Offset.disjoint _ (.inr (by decide)) (by unfold oEM1 frameBytes at *; omega) (by decide)
      ns := hp.sp.symm
      es := hp.es
      is := hgS
      sa := (hp.ks.sub_left (frame_sub s (by decide))).symm
      wo := by
        show (fb s + BitVec.ofNat 64 oEM1).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM1 frameBytes at *; omega
      wn := hp.wp
      we := hp.we
      wi := by have := hp.wg; rwa [hsig] at this
      ws := hp.ws }
  case spal => rw [ha.sp]; exact hfa
  case sp => rw [ha.sp]; unfold frameBytes at hfb; omega
  case hrd =>
    simp only [pdRd]
    rw [ha.g2, ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, hsa, ha.rd, ha.wr]
    have hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (kR s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    have hg : (⟨s.gpr .a7, (s.gpr .a3).toNat⟩ : Region) ∈ s.rd := by rw [hp.hrd, ← hsig]; simp
    refine Covers.cons (hm _ (by rw [hp.hrd]; simp)) (Covers.cons (hm _ (by rw [hp.hrd]; simp))
      (Covers.cons (hm _ hg) (Covers.one (in_fr' s _ _ (by decide)) |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g0, ha.g1, ha.sa0, ha.sa1, ha.wr]
    exact Covers.cons (Covers.one (in_fr s _ (by unfold oEM1 frameBytes; omega)))
      (Covers.of_mem fun x hx => by
        rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ (by rw [hp.hwr]; simp))
  case hk => rw [ha.g1]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g3, ha.g1]; exact hp.hp
  case h10 => rw [ha.g7, ha.g1]
  case he1 => rw [ha.g5]; exact hp.e1
  case he2 => rw [ha.g5, ha.g1]; exact hp.e2
  case hs => rw [ha.g1, ha.sa1]; exact hp.hs
  case al2 => rw [ha.g2]; exact hp.al3
  case al0 => rw [ha.sa0]; exact hp.al1

/-- After the call: `VMid`, and `EM₁` written with RSAVP1's result if `pre`
holds the modulus' values. -/
structure AfterCall (s t : State) : Prop extends
    Mid (sR s) s (s.gpr .a0) (s.gpr .a1) (s.gpr .a3) (zx (s.gpr .a6)) t where
  res : PreOk s →
    Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a3).toNat ((t.gpr .a0).setWidth 32) (pubOut s)

theorem call_ok {s t : State} (hp : PreR s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .a3) :
    WP isa pubCall t (AfterCall s) := by
  have hk2 := hp.k2
  refine pdCall (pdOk_of hp ha hsig) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g0, ha.g1, ha.sa0, ha.sa1] at hf
  have hfm := ha.toMid.frameMem hp.ks (e := oEM1) (n := (s.gpr .a3).toNat) (by decide)
    (by unfold oEM1 frameBytes; omega) hf
  have hfr0 : Frame [kR s, sR s] s.mem t.mem := ha.mem
  have hgK : (kR s).Disjoint ⟨s.gpr .a7, (s.gpr .a3).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .a7, (s.gpr .a3).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  refine { ha.toMid.of (fun r hr => hpres r (by revert r; decide)) hsp' hrd' hwr' hfm.1 hfm.2 with
    res := fun hc => ?_ }
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .a2) (t.gpr .a3).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    rw [ha.g2, ha.g3]; exact words_of_frame hfr0 hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (by rw [ha.g1, Proof.RsaPkcs1Sig.bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g0, ha.g1, ha.g4, ha.g5, ha.g6, bytes_of_frame hfr0 hp.ke hp.es.symm (by have := hp.we; omega),
    bytes_of_frame hfr0 hgK hgS.symm (by omega)] at this
  exact this

end Rec

end VG.Proof.RsaPkcs1Sig.RISCV64

/-!
# `vg_rsa_pkcs1_recover_precomputed` on RISC-V: the mask

Untrusted: everything here is checked by Lean. `maskLoop_ok`: the loop
masks each byte of `out` with the low byte of `a3`. `mask_eq`: `maskM`'s
arithmetic, all ones exactly when the comparison found the two encodings
equal and the call succeeded.
-/


namespace VG.Proof.RsaPkcs1Sig.RISCV64.Rec

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed VG.WriteBytes
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_take_succ writeBytes_out)

/-- `maskLoop` masks the `n` bytes at `a1 = p`, counted down in `a5`, with
the low byte of `a3`. -/
theorem maskLoop_ok {s : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h11 : s.gpr .a1 = p) (h8 : s.gpr .a5 = BitVec.ofNat 64 n)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa maskLoop s fun t => Kept [.t1, .a1, .a5] s t ∧
      t.mem = writeBytes s.mem p ((Spec.Rsa.bytesAt s.mem p n).map (· &&& (s.gpr .a3).setWidth 8)) := by
  refine WP.mono (wp_countdown (cnt := .a5) hn' hn
    (fun i t => Kept [.t1, .a1, .a5] s t ∧
      t.mem = writeBytes s.mem p (((Spec.Rsa.bytesAt s.mem p n).take i).map (· &&& (s.gpr .a3).setWidth 8)) ∧
      t.gpr .a1 = p + BitVec.ofNat 64 i) ?_
    ⟨Kept.refl _ _, by simp [writeBytes_nil], by simp [h11]⟩ h8) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h11'⟩ _
    simp only [List.cons_append, List.nil_append]
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .a1 + BitVec.ofNat 64 0) 1 := by
      rw [h11', hK.wr, BitVec.add_zero]
      obtain ⟨r, hr, hc⟩ := hw _ hi
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    have hlt : ((Spec.Rsa.bytesAt s.mem p n).take i).length = i := by
      simp [bytesAt_length]; omega_arith
    have hv : t.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ i (fun i' hi' => Offset.add_ofNat_ne p (by omega_arith) (by omega_arith) (by omega_arith))
        (by simp only [List.length_map, hlt]; omega_arith)]
    refine wp_lbu rfl hR fun s₁ o₁ e₁ => wp_and fun s₂ o₂ e₂ => ?_
    have hA : InRegions s₂.wr (s₂.gpr .a1 + BitVec.ofNat 64 0) 1 := by
      rw [o₂.wr, o₁.wr, o₂.get .a1, o₁.get .a1, h11', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_sb rfl hA fun s₃ m₃ => wp_addi (imm := 1) fun s₄ o₄ e₄ => wp_subi (imm := 1) fun s₅ o₅ e₅ =>
      wp_nil ?_
    have hK' : Kept [.t1, .a1, .a5] t s₅ :=
      (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩
    · rw [o₅.mem, o₄.mem, m₃.mem, e₂, o₂.mem, e₁, o₁.mem, o₁.get .a3, hK.get .a3, o₂.get .a1, o₁.get .a1,
        h11']
      simp only [BitVec.add_zero]
      rw [hv, BitVec.setWidth_and, byte_setWidth64, hm, bytesAt_take_succ _ _ hi, List.map_append, List.map_cons,
        List.map_nil, writeBytes_snoc _ _ _ _ (by simp only [List.length_map, hlt]; omega_arith), List.length_map, hlt]
    · rw [o₅.get .a1, e₄, m₃.gpr, o₂.get .a1, o₁.get .a1, h11', ofNat_succ']
    · rw [e₅, o₄.get .a5, m₃.gpr, o₂.get .a5, o₁.get .a5]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

/-- The sign bit of `0 - x` for a 32-bit `x`: whether `x` is not 0. -/
theorem neg_bit (x : BitVec 64) :
    (BitVec.ofNat 64 0 - (x <<< 32) >>> 32) >>> 63 = if x.setWidth 32 = 0 then 0 else 1 := by
  have e : (x <<< 32) >>> 32 = (x.setWidth 32).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    have h₁ : x.toNat * 2 ^ 32 % 2 ^ 64 = x.toNat % 2 ^ 32 * 2 ^ 32 := by
      rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mul_mod_mul_right]
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, h₁,
      Nat.mul_div_cancel _ (by decide), BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    omega_arith
  rw [e]
  by_cases h : x.setWidth 32 = 0
  · rw [h]; decide
  · rw [ite_eq_right h]
    have h' : (x.setWidth 32).toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    have hl := (x.setWidth 32).isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth]
    simp only [BitVec.toNat_setWidth] at h' hl
    simp; omega_arith

/-- The mask: all ones if `c`, else 0. -/
def maskOf (c : Prop) [Decidable c] : BitVec 64 := if c then BitVec.allOnes 64 else 0

theorem mask_eq (d : BitVec 64) (x : BitVec 64) (hd : d.toNat < 256) :
    BitVec.ofNat 64 0 - ((d - BitVec.ofNat 64 1) >>> 63 &&& (BitVec.ofNat 64 0 - (x <<< 32) >>> 32) >>> 63) =
      maskOf (d = 0 ∧ x.setWidth 32 ≠ 0) := by
  rw [borrow1 hd, neg_bit]
  unfold maskOf
  by_cases h₁ : d = 0 <;> by_cases h₂ : x.setWidth 32 = 0
  · rw [ite_eq_left h₁, ite_eq_left h₂, ite_eq_right (fun h => h.2 h₂)]; decide
  · rw [ite_eq_left h₁, ite_eq_right h₂, ite_eq_left ⟨h₁, h₂⟩]; decide
  · rw [ite_eq_right h₁, ite_eq_left h₂, ite_eq_right (fun h => h₁ h.1)]; decide
  · rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right (fun h => h₁ h.1)]; decide

theorem maskOf_byte (c : Prop) [Decidable c] (b : Byte) :
    b &&& (maskOf c).setWidth 8 = if c then b else 0 := by
  unfold maskOf
  split
  · rw [show (BitVec.allOnes 64).setWidth 8 = BitVec.allOnes 8 by decide, BitVec.and_allOnes]
  · simp

theorem maskOf_fin (c : Prop) [Decidable c] :
    (BitVec.ofNat 64 1 &&& maskOf c).setWidth 32 = if c then 1 else 0 := by
  unfold maskOf; split <;> decide

/-- Bytes under the mask: themselves or zeros. -/
theorem maskOf_bytes (c : Prop) [Decidable c] (D : List Byte) :
    D.map (· &&& (maskOf c).setWidth 8) = if c then D else List.replicate D.length 0 := by
  simp only [maskOf_byte]
  by_cases hc : c
  · simp [hc]
  · simp [hc, List.map_const']

end VG.Proof.RsaPkcs1Sig.RISCV64.Rec


namespace VG.Proof.RsaPkcs1Sig.RISCV64.Rec

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes ne_of_disjoint bytesAt_drop)

/-! ## The specification -/

/-- The hash function's number. -/
abbrev hid (s : State) : Nat := ((s.gpr .a6).setWidth 32).toNat

/-- The result and `out`, from the entry state `s`: the octets `recover`
returns, or zeros. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s → ∀ h, Spec.RsaPkcs1Sig.Hash.ofId (hid s) = some h →
    Spec.Rsa.written s'.mem (s.gpr .a0) (s.gpr .a1).toNat ((s'.gpr .a0).setWidth 32)
      (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) h
        (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)))

/-- `EM₁` after the call `t`. -/
abbrev em1 (s t : State) : List Byte := Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a3).toNat

/-- The encoding of `EM₁`'s last `out_len` bytes. -/
def encOut (s t : State) : Option (List Byte) :=
  encodeId (hid s) ((em1 s t).drop ((s.gpr .a3).toNat - (s.gpr .a1).toNat)) (s.gpr .a3).toNat

/-- `recover`, by encoding, as the call's result gives it. -/
theorem recover_eq {s t : State} (hp : PreR s) (hsig : stackArg s 0 = s.gpr .a3)
    (hres : Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a3).toNat ((t.gpr .a0).setWidth 32)
      (pubOut s)) {h : Spec.RsaPkcs1Sig.Hash} (hh : Spec.RsaPkcs1Sig.Hash.ofId (hid s) = some h) :
    Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) h
        (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat) =
      match pubOut s, encOut s t with
      | some em, some em' => if em = em' then some (em.drop ((s.gpr .a3).toNat - (s.gpr .a1).toNat)) else none
      | _, _ => none := by
  obtain ⟨h', hh', hL⟩ := hp.hh
  rw [hh] at hh'; cases hh'
  rw [Proof.RsaPkcs1Sig.recover_eq_recoverEnc, Proof.RsaPkcs1Sig.recoverEnc, bytesAt_length, bytesAt_length, hsig,
    ite_eq_left rfl]
  unfold encOut encodeId
  rw [hh, ← hL]
  change (match pubOut s with | some em => _ | none => none) = _
  cases hpo : pubOut s with
  | none => rfl
  | some em =>
    rw [hpo] at hres
    have he1 : em1 s t = em := hres.2
    rw [he1]
    dsimp only
    cases he : Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .a3).toNat - (s.gpr .a1).toNat)) (s.gpr .a3).toNat with
    | none => simp
    | some em' =>
      by_cases e : em = em'
      · subst e; simp
      · rw [ite_eq_right (fun h => e (Option.some.inj h).symm)]
        exact (ite_eq_right e).symm

/-! ## The steps -/

theorem freed_mem (n : Nat) (s : State) : (freed n s).mem = s.mem := rfl
theorem freed_gpr (n : Nat) (s : State) : (freed n s).gpr = s.gpr := rfl

theorem add_ofNat_sub (a : Addr) {k L : Nat} (h : L ≤ k) :
    a + BitVec.ofNat 64 k - BitVec.ofNat 64 L = a + BitVec.ofNat 64 (k - L) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem add_ofNat_ofNat (a : Addr) (d e : Nat) :
    a + BitVec.ofNat 64 d + BitVec.ofNat 64 e = a + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- `valPtr`: `a4 := EM₁ + k - out_len`, from `RMid`. -/
theorem valPtr_ok {s t : State} (hp : PreR s) (hm : RMid s t) (h12 : t.gpr .t0 = fb s) :
    WP isa (.block valPtr) t fun w => Only [.a4] t w ∧
      w.gpr .a4 = fb s + BitVec.ofNat 64 (oEM1 + ((s.gpr .a3).toNat - (s.gpr .a1).toNat)) := by
  have hL := hp.len_le; have hk := hp.k1
  refine wp_addi (imm := oEM1) fun w₁ o₁ e₁ => wp_add fun w₂ o₂ e₂ => wp_sub fun w₃ o₃ e₃ =>
    wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, ?_⟩
  have e6 : BitVec.ofNat 64 (s.gpr .a3).toNat = s.gpr .a3 := by simp
  have e4 : BitVec.ofNat 64 (s.gpr .a1).toNat = s.gpr .a1 := by simp
  rw [e₃, e₂, e₁, o₁.get .s3, o₂.get .s2, o₁.get .s2, hm.s3, hm.s2, h12, ← e6, ← e4, add_ofNat_ofNat,
    add_ofNat_sub _ (by omega_arith),
    show oEM1 + (s.gpr .a3).toNat - (s.gpr .a1).toNat = oEM1 + ((s.gpr .a3).toNat - (s.gpr .a1).toNat) by
      unfold oEM1; omega_arith]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s.gpr .a3).isLt, Nat.mod_eq_of_lt (s.gpr .a1).isLt]

/-- `zeroOut`: zeros to the `n` bytes at `a1 = p`, counted in `t5`, and 0
returned. -/
theorem zeroOut_ok {y : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (h4 : y.gpr .a1 = p)
    (h11 : y.gpr .t5 = BitVec.ofNat 64 n) (hw : ∀ i < n, InRegions y.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa zeroOut y fun z => Kept [.t0, .a1, .t5, .a0] y z ∧
      z.mem = writeBytes y.mem p (List.replicate n 0) ∧ z.gpr .a0 = 0 := by
  unfold zeroOut
  refine WP.seq (wp_li (imm := 0) (by decide) fun y₁ o₁ e₁ => wp_nil ?_)
  refine WP.seq (WP.mono (fill_ok (p := p) (n := n) (b := 0) hn hn' (by rw [o₁.get .a1, h4])
    (by rw [o₁.get .t5, h11]) (by rw [e₁]; rfl) (by rw [o₁.wr]; exact hw)) fun y₂ ⟨k₂, m₂⟩ => ?_)
  unfold ret0
  exact wp_li (imm := 0) (by decide) fun y₃ o₃ e₃ => wp_nil ⟨((o₁.keep.trans k₂).trans o₃.keep).mono,
    by rw [o₃.mem, m₂, o₁.mem], by rw [e₃]; rfl⟩

/-- `out` is writable in the frame. -/
theorem out_wr {s : State} (hp : PreR s) {i : Nat} (hi : i < (s.gpr .a1).toNat) :
    InRegions (kR s :: s.wr) (s.gpr .a0 + BitVec.ofNat 64 i) 1 :=
  ⟨oR s, List.mem_cons_of_mem _ (by rw [hp.hwr]; simp),
    Offset.contains_base _ (by omega_arith) (by have := hp.wo; omega_arith)⟩

theorem bytes_written {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hl : xs.length = n) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) q n = xs := by
  subst hl; exact bytesAt_writeBytes _ _ _ hn

theorem ofNat_a1 (s : State) : s.gpr .a1 = BitVec.ofNat 64 (s.gpr .a1).toNat := by simp

/-- Writes of `out` keep `Saves`. -/
theorem saves_out {s y z : State} {rs : List Reg} (hp : PreR s) (h : Saves s y) (o : Kept rs y z) {xs : List Byte}
    (hl : xs.length = (s.gpr .a1).toNat) (hm : z.mem = writeBytes y.mem (s.gpr .a0) xs)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Saves s z :=
  h.keep o (R := [oR s]) (by have := frame_writeBytes y.mem (s.gpr .a0) xs; rw [hl] at this; rw [hm]; exact this)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ko) hrs

/-- The zeros of `zeroKept`, from `RMid`. -/
theorem zeroKept_ok {s w : State} (hp : PreR s) (hm : RMid s w) :
    WP isa zeroKept w fun z => Saves s z ∧ z.gpr .a0 = 0 ∧
      Spec.Rsa.bytesAt z.mem (s.gpr .a0) (s.gpr .a1).toNat = List.replicate (s.gpr .a1).toNat 0 := by
  have hL1 := hp.len_pos; have hL2 := hp.len_le
  unfold zeroKept
  refine WP.seq (wp_mov fun y₁ p₁ f₁ => wp_mov fun y₂ p₂ f₂ => wp_nil ?_)
  have O₂ : Only [.a1, .t5] w y₂ := p₁.trans p₂
  refine WP.mono (zeroOut_ok (p := s.gpr .a0) (n := (s.gpr .a1).toNat) hL1 (by omega_arith)
    (by rw [p₂.get .a1, f₁, hm.s1]) (by rw [f₂, p₁.get .s2, hm.s2, ← ofNat_a1])
    (fun i hi => by rw [O₂.wr, hm.wr]; exact out_wr hp hi)) fun z ⟨kz, mz, rz⟩ => ⟨?_, rz, ?_⟩
  · exact saves_out hp (hm.only O₂).saves kz (by simp) mz
  · rw [mz, bytes_written (by simp) (by omega_arith)]

/-- The hash value's place in `EM₁`. -/
abbrev dig (s : State) : Addr := fb s + BitVec.ofNat 64 (oEM1 + ((s.gpr .a3).toNat - (s.gpr .a1).toNat))

/-- The hash value's place is in the frame. -/
theorem dig_in {s : State} (hp : PreR s) (rd rs : List Region) {j : Nat} (hj : j < (s.gpr .a1).toNat) :
    InRegions (rd ++ kR s :: rs) (dig s + BitVec.ofNat 64 j) 1 := by
  have := hp.k1; have := hp.k2; have := hp.len_le
  rw [add_ofNat_ofNat]; exact in_fr' s _ _ (by unfold oEM1 frameBytes; omega_arith)

theorem dig_sub {s : State} (hp : PreR s) : Region.Sub ⟨dig s, (s.gpr .a1).toNat⟩ (kR s) := by
  have := hp.k1; have := hp.k2; have := hp.len_le
  exact frame_sub s (by unfold oEM1 frameBytes; omega_arith)

/-- After the comparison, its difference in `t4`: `out` gets the hash
value's bytes `D` if they encode to `EM₁` and the call succeeded (its status
`st`), zeros if not, and the result says which. -/
theorem release_ok {s y : State} {st : BitVec 64} {D : List Byte} (hp : PreR s) (hm : RMid s y)
    (hst : y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = st)
    (hD : Spec.Rsa.bytesAt y.mem (dig s) (s.gpr .a1).toNat = D) (hlt : (y.gpr .t4).toNat < 256) :
    WP isa release y fun x => Saves s x ∧
      (x.gpr .a0).setWidth 32 = (if y.gpr .t4 = 0 ∧ st.setWidth 32 ≠ 0 then 1 else 0) ∧
      Spec.Rsa.bytesAt x.mem (s.gpr .a0) (s.gpr .a1).toNat =
        if y.gpr .t4 = 0 ∧ st.setWidth 32 ≠ 0 then D else List.replicate (s.gpr .a1).toNat 0 := by
  have hk1 := hp.k1; have hk2 := hp.k2; have hL1 := hp.len_pos; have hL2 := hp.len_le
  have hDl : D.length = (s.gpr .a1).toNat := by rw [← hD, bytesAt_length]
  unfold release maskM
  simp only [zext, List.cons_append, List.nil_append]
  refine WP.seq (wp_subi (imm := 1) fun z₁ q₁ g₁ => wp_srl fun z₂ q₂ g₂ => wp_addSp fun z₃ q₃ g₃ => ?_)
  rw [q₂.sp, q₁.sp, hm.sp, BitVec.add_zero] at g₃
  refine wp_ld (a := fb s + BitVec.ofNat 64 oSt) (by rw [g₃]) (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [q₃.rd, q₂.rd, q₁.rd, q₃.wr, q₂.wr, q₁.wr, hm.wr]; exact in_fr' s _ _ (by decide))
    fun z₄ q₄ g₄ => ?_
  refine wp_sll fun z₅ q₅ g₅ => wp_srl fun z₆ q₆ g₆ => wp_li (imm := 0) (by decide) fun z₇ q₇ g₇ =>
    wp_sub fun z₈ q₈ g₈ => wp_srl fun z₉ q₉ g₉ => wp_and fun z₁₀ q₁₀ g₁₀ => wp_sub fun z₁₁ q₁₁ g₁₁ => ?_
  have Q₃ : Only [.a1, .t0] y z₃ := (q₁.trans (q₂.trans q₃)).mono
  have Q₁₁ : Only [.a2, .a3, .a1] z₃ z₁₁ :=
    (q₄.trans (q₅.trans (q₆.trans (q₇.trans (q₈.trans (q₉.trans (q₁₀.trans q₁₁))))))).mono
  have M₁₁ : z₁₁.gpr .a1 = maskOf (y.gpr .t4 = 0 ∧ st.setWidth 32 ≠ 0) := by
    rw [g₁₁, g₁₀, q₁₀.get .a3, q₉.get .a3, q₉.get .a1, g₉, q₈.get .a3, q₈.get .a1, g₈, g₇, q₇.get .a1,
      q₇.get .a2, g₆, q₆.get .a1, g₅, q₅.get .a1, g₄, q₄.get .a1, q₃.get .a1, q₃.mem, q₂.mem, q₁.mem, hst, g₂, g₁]
    exact mask_eq _ _ hlt
  have t0₁₁ : z₁₁.gpr .t0 = fb s := by rw [Q₁₁.get .t0, g₃]
  refine wp_sd (a := fb s + BitVec.ofNat 64 oMk) (by rw [t0₁₁]) (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [Q₁₁.wr, Q₃.wr, hm.wr]; exact in_fr s _ (by decide)) fun z₁₂ m₁₂ => wp_nil ?_
  have fr₁₂ : Frame [⟨fb s + BitVec.ofNat 64 oMk, 8⟩] z₁₁.mem z₁₂.mem := by
    rw [m₁₂.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have mid₁₂ : RMid s z₁₂ := ((hm.only Q₃).only Q₁₁).frameW1 m₁₂.keep hp.ks (by decide) (by decide) fr₁₂
  have slot₁₂ : z₁₂.mem.readW (fb s + BitVec.ofNat 64 oMk) 64 = maskOf (y.gpr .t4 = 0 ∧ st.setWidth 32 ≠ 0) := by
    rw [m₁₂.mem, Mem.readW_writeW_self64, M₁₁]
  have D₁₂ : Spec.Rsa.bytesAt z₁₂.mem (dig s) (s.gpr .a1).toNat = D := by
    rw [Proof.RsaPkcs1Sig.bytes_apart (R := ⟨dig s, (s.gpr .a1).toNat⟩) fr₁₂
      (Offset.disjoint _ (.inr (by unfold oMk oEM1; omega_arith)) (by unfold oEM1; omega_arith) (by decide))
      (by dsimp only; omega_arith), Q₁₁.mem, Q₃.mem, hD]
  -- the value to `out`
  refine WP.seq ?_
  unfold copyOut
  refine WP.seq (WP.block_append_iff.mpr (wp_mov fun c₁ r₁ h₁ => wp_mov fun c₂ r₂ h₂ => wp_nil ?_))
  have midc₂ : RMid s c₂ := mid₁₂.only (r₁.trans r₂)
  have t0c₂ : c₂.gpr .t0 = fb s := by rw [r₂.get .t0, r₁.get .t0, m₁₂.gpr, t0₁₁]
  refine WP.mono (valPtr_ok hp midc₂ t0c₂) fun c₃ ⟨oc₃, ec₃⟩ => ?_
  have midc₃ : RMid s c₃ := midc₂.only oc₃
  have Dc₃ : Spec.Rsa.bytesAt c₃.mem (dig s) (s.gpr .a1).toNat = D := by rw [oc₃.mem, r₂.mem, r₁.mem]; exact D₁₂
  refine WP.mono (copy_ok (p := s.gpr .a0) (q := dig s) (n := (s.gpr .a1).toNat) hL1 (by omega_arith)
    (by rw [oc₃.get .a1, r₂.get .a1, h₁, mid₁₂.s1]) ec₃
    (by rw [oc₃.get .a5, h₂, r₁.get .s2, mid₁₂.s2, ← ofNat_a1])
    (fun j hj => by rw [midc₃.rd, midc₃.wr]; exact dig_in hp _ _ hj)
    (fun i hi => by rw [midc₃.wr]; exact out_wr hp hi)
    (fun j hj i hi => ne_of_disjoint (hp.ko.sub_left (dig_sub hp)) (by omega_arith) (by omega_arith) hj hi))
    fun c₄ ⟨kc₄, mc₄⟩ => ?_
  have svc₄ : Saves s c₄ := saves_out hp midc₃.saves kc₄ (bytesAt_length _ _ _) mc₄
  have outc₄ : Spec.Rsa.bytesAt c₄.mem (s.gpr .a0) (s.gpr .a1).toNat = D := by
    rw [mc₄, bytes_written (bytesAt_length _ _ _) (by omega_arith), Dc₃]
  have slotc₄ : c₄.mem.readW (fb s + BitVec.ofNat 64 oMk) 64 = maskOf (y.gpr .t4 = 0 ∧ st.setWidth 32 ≠ 0) := by
    have hf := frame_writeBytes c₃.mem (s.gpr .a0) (Spec.Rsa.bytesAt c₃.mem (dig s) (s.gpr .a1).toNat)
    rw [bytesAt_length] at hf
    rw [mc₄, hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.ko.sub_left (frame_sub s (d := oMk) (n := 8) (by decide))) (by decide), oc₃.mem, r₂.mem,
      r₁.mem, slot₁₂]
  -- the mask's registers
  unfold maskArgs
  refine WP.seq (wp_addSp fun d₁ n₁ k₁ => ?_)
  rw [svc₄.sp, BitVec.add_zero] at k₁
  refine wp_ld (a := fb s + BitVec.ofNat 64 oMk) (by rw [k₁]) (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [n₁.rd, n₁.wr, svc₄.wr]; exact in_fr' s _ _ (by decide)) fun d₂ n₂ k₂ =>
    wp_mov fun d₃ n₃ k₃ => wp_mov fun d₄ n₄ k₄ => wp_nil ?_
  have N₄ : Only [.t0, .a3, .a1, .a5] c₄ d₄ := n₁.trans (n₂.trans (n₃.trans n₄))
  have svd₄ : Saves s d₄ := svc₄.keep N₄.keep (R := []) (by rw [N₄.mem]; exact Frame.refl _ _)
    (fun r h => nomatch h)
  have r9d₄ : d₄.gpr .a3 = maskOf (y.gpr .t4 = 0 ∧ st.setWidth 32 ≠ 0) := by
    rw [n₄.get .a3, n₃.get .a3, k₂, n₁.mem, slotc₄]
  refine WP.seq (WP.mono (maskLoop_ok (p := s.gpr .a0) (n := (s.gpr .a1).toNat) hL1 (by omega_arith)
    (by rw [n₄.get .a1, k₃, n₂.get .s1, n₁.get .s1, kc₄.get .s1, midc₃.s1])
    (by rw [k₄, n₃.get .s2, n₂.get .s2, n₁.get .s2, kc₄.get .s2, midc₃.s2, ← ofNat_a1])
    (fun i hi => by rw [svd₄.wr]; exact out_wr hp hi)) fun e₁ ⟨ke₁, me₁⟩ => ?_)
  rw [r9d₄, N₄.mem, outc₄, maskOf_bytes, hDl] at me₁
  unfold fin
  refine wp_li (imm := 1) (by decide) fun f₁ p₁ h₁ => wp_and fun f₂ p₂ h₂ => wp_nil ⟨?_, ?_, ?_⟩
  · refine saves_out hp svd₄ (ke₁.trans (p₁.keep.trans p₂.keep)) (xs := if y.gpr .t4 = 0 ∧ st.setWidth 32 ≠ 0 then
      D else List.replicate (s.gpr .a1).toNat 0) (by split <;> simp [hDl]) (by rw [p₂.mem, p₁.mem, me₁, N₄.mem])
  · rw [h₂, h₁, p₁.get .a3, ke₁.get .a3, r9d₄, maskOf_fin]
  · rw [p₂.mem, p₁.mem, me₁, bytes_written (by split <;> simp [hDl]) (by omega_arith)]

theorem encodeId_length {x : Nat} {H em : List Byte} {k : Nat} (h : encodeId x H k = some em) :
    em.length = k := by
  unfold encodeId at h
  split at h
  · exact Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- After the call: the status kept, the encoding, the value to `out` or
zeros, and the restores. -/
theorem afterPub_ok {s t : State} (hp : PreR s) (hsig : stackArg s 0 = s.gpr .a3) (ha : AfterCall s t) :
    WP isa (.seq (.block encArgs) (.seq encode (.seq tail (.block restore)))) t
      fun w => Post s (freed frameBytes w) := by
  have hk1 := hp.k1; have hk2 := hp.k2; have hL1 := hp.len_pos; have hL2 := hp.len_le
  have hfa := fb_al hp.spal hp.sp1
  have hfin : ∀ y : State, Saves s y → (PreOk s → ∀ h,
      Spec.RsaPkcs1Sig.Hash.ofId (hid s) = some h →
      Spec.Rsa.written y.mem (s.gpr .a0) (s.gpr .a1).toNat ((y.gpr .a0).setWidth 32)
        (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) h
          (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat))) →
      WP isa (.block restore) y fun w => Post s (freed frameBytes w) :=
    fun y hy hw => WP.mono (restore_ok hy (by omega)) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hc h hh => by
      rw [freed_mem, freed_gpr, hm, h3]; exact hw hc h hh⟩
  unfold encArgs
  refine WP.seq (WP.block_append_iff.mpr (wp_addSp fun u₁ o₁ e₁ => ?_))
  rw [ha.sp, BitVec.add_zero] at e₁
  refine wp_sd (a := fb s + BitVec.ofNat 64 oSt) (by rw [e₁]) (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁.wr, ha.wr]; exact in_fr s _ (by decide)) fun u₂ m₂ => ?_
  refine wp_addi (imm := oEM2) fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ =>
    wp_mov fun u₆ o₆ e₆ => wp_nil ?_
  have fr₂ : Frame [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem u₂.mem := by
    rw [m₂.mem, o₁.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have mid₂ : RMid s u₂ := ha.toMid.frameW1 (o₁.keep.trans m₂.keep) hp.ks (by decide) (by decide) fr₂
  have O₆ : Only [.a1, .a2, .a3, .a5] u₂ u₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have mid₆ : RMid s u₆ := mid₂.only O₆
  have t0₆ : u₆.gpr .t0 = fb s := by rw [O₆.get .t0, m₂.gpr, e₁]
  refine WP.mono (valPtr_ok hp mid₆ t0₆) fun u₉ ⟨o₉, e₉⟩ => ?_
  have mid₉ : RMid s u₉ := mid₆.only o₉
  have r4₉ : u₉.gpr .a1 = fb s + BitVec.ofNat 64 oEM2 := by
    rw [o₉.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, e₃, m₂.gpr, e₁]
  have r5₉ : u₉.gpr .a2 = s.gpr .a3 := by rw [o₉.get .a2, o₆.get .a2, o₅.get .a2, e₄, o₃.get .s3, mid₂.s3]
  have r6₉ : u₉.gpr .a3 = zx (s.gpr .a6) := by
    rw [o₉.get .a3, o₆.get .a3, e₅, o₄.get .s4, o₃.get .s4, mid₂.s4]
  have r8₉ : u₉.gpr .a5 = s.gpr .a1 := by rw [o₉.get .a5, e₆, o₅.get .s2, o₄.get .s2, o₃.get .s2, mid₂.s2]
  have slot₂ : u₂.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .a0 := by
    rw [m₂.mem, Mem.readW_writeW_self64, o₁.get .a0]
  have em1₂ : Spec.Rsa.bytesAt u₂.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a3).toNat = em1 s t :=
    Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) fr₂
      (Offset.disjoint _ (.inr (by decide)) (by unfold oEM1; omega_arith) (by decide)) (by dsimp only; omega_arith)
  have hpre : EPre u₉ (hid s) (s.gpr .a3).toNat := {
    r6 := by rw [r6₉, zx_toNat]
    hk := by rw [r5₉]
    kle := hk2
    buf := fun i hi => by
      rw [mid₉.wr, r4₉, add_ofNat_ofNat]
      exact in_fr s _ (by unfold oEM2 frameBytes; omega_arith)
    rd := fun j hj => by
      rw [r8₉] at hj
      rw [mid₉.rd, mid₉.wr, e₉]; exact dig_in hp _ _ hj
    sep := fun j hj i hi => by
      rw [r8₉] at hj
      rw [e₉, r4₉, add_ofNat_ofNat, add_ofNat_ofNat]
      exact Offset.add_ofNat_ne _ (by unfold oEM1; omega_arith) (by unfold oEM2; omega_arith)
        (by unfold oEM1 oEM2; omega_arith) }
  have hD₉ : Spec.Rsa.bytesAt u₉.mem (dig s) (s.gpr .a1).toNat =
      (em1 s t).drop ((s.gpr .a3).toNat - (s.gpr .a1).toNat) := by
    rw [o₉.mem, O₆.mem, dig, ← add_ofNat_ofNat, ← bytesAt_drop, Nat.sub_add_cancel (by omega_arith), em1₂]
  have hH : Spec.Rsa.bytesAt u₉.mem (u₉.gpr .a4) (u₉.gpr .a5).toNat =
      (em1 s t).drop ((s.gpr .a3).toNat - (s.gpr .a1).toNat) := by
    rw [e₉, r8₉]; exact hD₉
  refine WP.seq (WP.mono (encode_ok hpre) fun w ⟨hK, hout⟩ => ?_)
  rw [hH] at hout
  change EOut u₉ w (encOut s t) at hout
  refine WP.seq ?_
  unfold tail
  cases heo : encOut s t with
  | none =>
    rw [heo] at hout
    obtain ⟨h0, hme⟩ := hout
    have midw : RMid s w := mid₉.frameW1 hK hp.ks (e := oEM2) (n := 1024) (by decide) (by decide)
      (by rw [hme]; exact Frame.refl _ _)
    refine WP.ite true ((eval_zero w .a0).trans (by rw [h0]; rfl)) (fun _ => WP.mono (zeroKept_ok hp midw)
      fun y ⟨hy, r3y, oy⟩ => hfin y hy fun hc h hh => ?_) (by simp)
    rw [recover_eq hp hsig (ha.res hc) hh, heo, r3y]
    cases pubOut s <;> exact ⟨rfl, oy⟩
  | some em' =>
    rw [heo] at hout
    obtain ⟨h1, hme⟩ := hout
    refine WP.ite false ((eval_zero w .a0).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
    have hl' : em'.length = (s.gpr .a3).toNat := encodeId_length heo
    have fw : Frame [⟨fb s + BitVec.ofNat 64 oEM2, 1024⟩] u₉.mem w.mem := by
      rw [hme, r4₉]
      exact (frame_writeBytes _ _ _).sub fun r hr => by
        rw [List.mem_singleton.mp hr, hl']; exact ⟨_, List.mem_singleton_self _, Region.sub_prefix hk2⟩
    have midw : RMid s w := mid₉.frameW1 hK hp.ks (by decide) (by decide) fw
    have slotw : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .a0 := by
      rw [fw.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)) (by decide), o₉.mem, O₆.mem, slot₂]
    have hDw : Spec.Rsa.bytesAt w.mem (dig s) (s.gpr .a1).toNat =
        (em1 s t).drop ((s.gpr .a3).toNat - (s.gpr .a1).toNat) := by
      rw [Proof.RsaPkcs1Sig.bytes_apart (R := ⟨dig s, (s.gpr .a1).toNat⟩) fw
        (Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1; omega_arith) (by decide))
        (by dsimp only; omega_arith), hD₉]
    unfold cmpArgs
    refine WP.seq (wp_addSp fun v₁ p₁ f₁ => wp_addi (imm := oEM1) fun v₂ p₂ f₂ =>
      wp_addi (imm := oEM2) fun v₃ p₃ f₃ => wp_mov fun v₄ p₄ f₄ => wp_nil ?_)
    rw [midw.sp, BitVec.add_zero] at f₁
    have P₄ : Only [.t0, .a1, .a2, .a3] w v₄ := p₁.trans (p₂.trans (p₃.trans p₄))
    have midv : RMid s v₄ := midw.only P₄
    have x4 : v₄.gpr .a1 = fb s + BitVec.ofNat 64 oEM1 := by rw [p₄.get .a1, p₃.get .a1, f₂, f₁]
    have x5 : v₄.gpr .a2 = fb s + BitVec.ofNat 64 oEM2 := by rw [p₄.get .a2, f₃, p₂.get .t0, f₁]
    have x6 : v₄.gpr .a3 = BitVec.ofNat 64 (s.gpr .a3).toNat := by
      rw [f₄, p₃.get .s3, p₂.get .s3, p₁.get .s3, midw.s3]; simp
    have hin : ∀ {d : Nat}, d + (s.gpr .a3).toNat ≤ frameBytes → ∀ j < (s.gpr .a3).toNat,
        InRegions (v₄.rd ++ v₄.wr) (fb s + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 := fun hd j hj => by
      rw [midv.wr, add_ofNat_ofNat]
      exact in_fr' s _ _ (by omega_arith)
    refine WP.seq (WP.mono (compare_ok (s := v₄) (n := (s.gpr .a3).toNat) (by omega_arith) (by omega_arith) x6
      (fun j hj => by rw [x4]; exact hin (by unfold oEM1 frameBytes; omega_arith) j hj)
      (fun j hj => by rw [x5]; exact hin (by unfold oEM2 frameBytes; omega_arith) j hj))
      fun y ⟨oy, hiff, hlt⟩ => ?_)
    have midy : RMid s y := midv.only oy
    have hb1 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a3).toNat = em1 s t := by
      rw [P₄.mem, hme, r4₉, o₉.mem, O₆.mem, ← em1₂]
      refine Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) (frame_writeBytes _ _ _) ?_ (by dsimp only; omega_arith)
      rw [hl']
      exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1; omega_arith)
        (by unfold oEM2; omega_arith)
    have hb2 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .a3).toNat = em' := by
      rw [P₄.mem, hme, r4₉, bytes_written hl' (by omega_arith)]
    rw [x4, x5, hb1, hb2] at hiff
    refine WP.mono (release_ok (st := t.gpr .a0)
      (D := (em1 s t).drop ((s.gpr .a3).toNat - (s.gpr .a1).toNat)) hp midy (by rw [oy.mem, P₄.mem, slotw])
      (by rw [oy.mem, P₄.mem, hDw]) hlt) fun x ⟨hx, r3x, outx⟩ => hfin x hx fun hc h hh => ?_
    rw [recover_eq hp hsig (ha.res hc) hh, heo]
    have hres := ha.res hc
    cases hpo : pubOut s with
    | none =>
      rw [hpo] at hres
      have hc' : ¬ (y.gpr .t4 = 0 ∧ (t.gpr .a0).setWidth 32 ≠ 0) := fun h => h.2 hres.1
      rw [ite_eq_right hc'] at r3x outx
      exact ⟨r3x, outx⟩
    | some em =>
      rw [hpo] at hres
      have he1 : em1 s t = em := hres.2
      dsimp only
      by_cases e : em = em'
      · have hc' : y.gpr .t4 = 0 ∧ (t.gpr .a0).setWidth 32 ≠ 0 :=
          ⟨hiff.mpr (by rw [he1]; exact e), by rw [hres.1]; decide⟩
        rw [ite_eq_left hc'] at r3x outx
        rw [ite_eq_left e]
        exact ⟨r3x, by rw [outx, he1]⟩
      · have hc' : ¬ (y.gpr .t4 = 0 ∧ (t.gpr .a0).setWidth 32 ≠ 0) := fun h => e (by rw [← he1]; exact hiff.mp h.1)
        rw [ite_eq_right hc'] at r3x outx
        rw [ite_eq_right e]
        exact ⟨r3x, outx⟩

/-! ## The whole function -/

theorem lenCheck_ok {s : State} (hp : PreR s) :
    WP isa (.block (lenCheck .a3)) s fun t₁ => Only [.t0] s t₁ ∧ t₁.gpr .t0 = stackArg s 0 - s.gpr .a3 := by
  refine wp_addSp fun t₀ o₀ e₀ => wp_ld (a := stackArgAddr s 0) (by rw [e₀, BitVec.add_zero]; rfl)
    (arg_al hp.spal 0) (by rw [o₀.rd, o₀.wr]; exact arg_rd hp _ (by decide)) fun t₁ o₁ e₁ =>
    wp_sub fun t₂ o₂ e₂ => wp_nil ⟨(o₀.trans (o₁.trans o₂)).mono, ?_⟩
  rw [e₂, e₁, o₁.get .a3, o₀.get .a3, o₀.mem]; rfl

theorem eval_len {s t : State} (e : t.gpr .t0 = stackArg s 0 - s.gpr .a3) :
    isa.eval (.nonzero .t0) t = some (decide (stackArg s 0 ≠ s.gpr .a3)) := by
  rw [eval_nonzero, e, ne_zero_iff, BitVec.toNat_sub]
  have := (stackArg s 0).isLt; have := (s.gpr .a3).isLt
  refine congrArg some (decide_eq_decide.mpr ⟨fun h e => ?_, fun h e => h ?_⟩)
  · rw [e] at h; omega_arith
  · apply BitVec.eq_of_toNat_eq; omega_arith

theorem recover_len {s : State} (h : stackArg s 0 ≠ s.gpr .a3) (hh : Spec.RsaPkcs1Sig.Hash) :
    Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) hh
      (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat) = none := by
  unfold Spec.RsaPkcs1Sig.recover
  rw [bytesAt_length, bytesAt_length, ite_eq_right fun e => h (BitVec.eq_of_toNat_eq e)]

theorem code_ok {s : State} (hp : PreR s) : WP isa code s (Post s) := by
  have hL1 := hp.len_pos; have hL2 := hp.len_le
  unfold code
  refine WP.seq (WP.mono (lenCheck_ok hp) fun t₁ ⟨o₁, e₁⟩ => ?_)
  have hne := eval_len e₁
  by_cases hsig : stackArg s 0 = s.gpr .a3
  · refine WP.ite false (by rw [hne]; simp [hsig]) (by simp) fun _ => ?_
    refine WP.allocLe (by decide) (by rw [o₁.sp]; exact hp.sp1) ?_
    unfold body
    refine WP.seq (WP.mono (pubArgs_ok hp (by show t₁.sp - _ = _; rw [o₁.sp])
      (by show (⟨t₁.sp - _, _⟩ :: t₁.wr) = _; rw [o₁.sp, o₁.wr])
      (by show t₁.rd = _; rw [o₁.rd])
      (by show Frame _ _ t₁.mem; rw [o₁.mem]; exact Frame.refl _ _)
      (fun r hr => o₁.gpr r hr)) fun t₂ h₂ => ?_)
    exact WP.seq (WP.mono (call_ok hp h₂ hsig) fun t₃ h₃ => afterPub_ok hp hsig h₃)
  · refine WP.ite true (by rw [hne]; simp [hsig]) (fun _ => ?_) (by simp)
    unfold zeroArgs
    refine WP.seq (wp_mov fun y₁ p₁ f₁ => wp_mov fun y₂ p₂ f₂ => wp_nil ?_)
    have O₂ : Only [.t0, .t5, .a1] s y₂ := o₁.trans (p₁.trans p₂)
    refine WP.mono (zeroOut_ok (p := s.gpr .a0) (n := (s.gpr .a1).toNat) hL1 (by omega_arith)
      (by rw [f₂, p₁.get .a0, o₁.get .a0]) (by rw [p₂.get .t5, f₁, o₁.get .a1, ← ofNat_a1])
      (fun i hi => by
        rw [O₂.wr]
        exact ⟨oR s, by rw [hp.hwr]; simp, Offset.contains_base _ (by omega_arith) (by have := hp.wo; omega_arith)⟩))
      fun w ⟨kw, mw, rw₃⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun _ h _ => ?_⟩
    · exact (O₂.keep.trans kw).gpr r (by revert r; decide)
    · rw [kw.sp, O₂.sp]
    · exact (O₂.keep.trans kw).gpr .ra (by decide)
    · rw [recover_len hsig, rw₃, mw]
      exact ⟨rfl, bytes_written (by simp) (by omega_arith)⟩

/-- The correctness of `vg_rsa_pkcs1_recover_precomputed`, against its
shared contract. -/
theorem code_correct (s : State) (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok (preR_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  exact hr

end VG.Proof.RsaPkcs1Sig.RISCV64.Rec
