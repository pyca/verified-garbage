module

public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Frame
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Frame
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Callee
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverMask
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-! ### `RsaPkcs1Sig.PPC64LE.RecoverCall`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.PPC64LE.RecoverPre`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_recover_precomputed` on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreR s`: the shared
contract's precondition (`recoverPrecomputedContract`, with the stack of the
frame, `frameBytes`), by name (`preR_of`). As `vg_rsa_pkcs1_verify_precomputed`'s
(`VerifyPre.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

/-- The buffers: `out`, `n`, `e`, the signature and the precomputed values
(the working space, the arguments on the stack and the stack the function
uses are `sR`, `aR` and `kR`). -/
abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev gR (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

/-- What the code needs of `recoverPrecomputedContract.pre`, by name. -/
structure PreR (s : State) : Prop where
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 136 ≤ 2 ^ 64
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
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wn : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  we : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wg : (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  ws : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r6).toNat
  k2 : (s.gpr .r6).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .r8).toNat
  e2 : (s.gpr .r8).toNat ≤ (s.gpr .r6).toNat
  hh : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .r9).setWidth 32).toNat = some h ∧ (s.gpr .r4).toNat = h.len
  hs : Spec.Rsa.publicScratchWords (s.gpr .r6).toNat ≤ (stackArg s 2).toNat
  hp : (stackArg s 4).toNat = Spec.Rsa.precomputedWords (s.gpr .r6).toNat

theorem preR_of {s : State} (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes).pre s) : PreR s := by
  have e : frameBytes = 2223 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, og, os, op, oa, ns, es, gs, sp, sa, ko, kn, ke, kg, ks, kp, ka, wo, wn, we,
    wg, ws, wp, ⟨k1, k2⟩, e1, e2, hh, hs, hp⟩ := h
  exact ⟨sp1, by omega_using [sp2], hrd, hwr, on, oe, og, os, op, oa, ns, es, gs, sp, sa, ko, kn, ke, kg, ks, kp, ka, wo, wn,
    we, wg, ws, wp, k1, k2, e1, e2, hh, hs, hp⟩

/-- The hash's length, at least one octet. -/
theorem PreR.len_pos {s : State} (hp : PreR s) : 1 ≤ (s.gpr .r4).toNat := by
  obtain ⟨h, -, e⟩ := hp.hh
  rw [e]; cases h <;> decide

/-- The hash's length, at most 64 octets. -/
theorem PreR.len_le {s : State} (hp : PreR s) : (s.gpr .r4).toNat ≤ 64 := by
  obtain ⟨h, -, e⟩ := hp.hh
  rw [e]; cases h <;> decide

end VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

end

end


/-!
# `vg_rsa_pkcs1_recover_precomputed` on PPC64LE: the call

As `vg_rsa_pkcs1_verify_precomputed`'s (`VerifyCall.lean`): `pubArgs_ok`, the
block before the call, keeps `out`, `out_len`, `k` and `hash` in `r28`–`r31`
and sets up the call of `vg_rsa_public_precomputed_checked` (`AtCall`);
`call_ok`, the call writes RSAVP1's result to `EM₁` if `pre` holds the
modulus' values (`AfterCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed

/-- In the frame, `out`, `out_len`, `k` and `hash` kept. -/
abbrev RMid (s t : State) : Prop :=
  Mid (sR s) s (s.gpr .r3) (s.gpr .r4) (s.gpr .r6) ((s.gpr .r9).setWidth 32 |>.setWidth 64) t

/-- At the call: the arguments of `vg_rsa_public_precomputed_checked`, `EM₁`,
`n_len`, `pre`, `pre_len`, `e`, `e_len`, `sig` and `n_len`, and on the stack
`scratch` and `scratch_len`. -/
structure AtCall (s t : State) : Prop extends
    Mid (sR s) s (s.gpr .r3) (s.gpr .r4) (s.gpr .r6) ((s.gpr .r9).setWidth 32 |>.setWidth 64) t where
  g3 : t.gpr .r3 = fb s + BitVec.ofNat 64 oEM1
  g4 : t.gpr .r4 = s.gpr .r6
  g5 : t.gpr .r5 = stackArg s 3
  g6 : t.gpr .r6 = stackArg s 4
  g7 : t.gpr .r7 = s.gpr .r7
  g8 : t.gpr .r8 = s.gpr .r8
  g9 : t.gpr .r9 = s.gpr .r10
  g10 : t.gpr .r10 = s.gpr .r6
  a0 : stackArg t 0 = stackArg s 1
  a1 : stackArg t 1 = stackArg s 2

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

theorem pubArgs_ok {s u : State} (hp : PreR s) (hsp : u.sp = fb s) (hwr : u.wr = fr s :: s.wr)
    (hrd : u.rd = s.rd) (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r, r ∉ [Reg.r11, .r12] → u.gpr r = s.gpr r)
    (hlr : u.lr = s.lr) :
    WP isa (.block pubArgs) u (AtCall s) := by
  unfold pubArgs
  rw [List.append_assoc]
  refine save_ok hsp hwr hm (fun r hr => hg r (by revert r; decide)) hlr fun v kv v12 fv sv lv => ?_
  obtain gv : ∀ r, r ∉ [Reg.r12, .r0, .r11] → v.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kv.gpr r (by simp [hr.1, hr.2.1]), hg r (by simp [hr.1, hr.2.2])]
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_lsrw fun v₄ o₄ e₄ =>
    wp_mov fun v₅ o₅ e₅ => wp_mov fun v₆ o₆ e₆ => wp_mov fun v₈ o₈ e₈ => ?_
  obtain O₈ : Only [.r28, .r29, .r30, .r31, .r9, .r10, .r4] v v₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₈)))))).mono
  obtain r12₈ : v₈.gpr .r12 = fb s := by rw [O₈.get .r12, v12]
  obtain rd₈ : v₈.rd = s.rd := by rw [O₈.rd, kv.rd, hrd]
  obtain wr₈ : v₈.wr = fr s :: s.wr := by rw [O₈.wr, kv.wr, hwr]
  obtain sp₈ : v₈.sp = fb s := by rw [O₈.sp, kv.sp, hsp]
  unfold callTail
  refine wp_ld (a := stackArgAddr s 1) (by rw [r12₈, stackArgAddr_fb]) (by rw [rd₈]; exact arg_rd hp _ (by decide))
    fun v₉ o₉ e₉ => ?_
  rw [O₈.mem, arg_frame hp fv (by decide)] at e₉
  refine wp_std (a := fb s + BitVec.ofNat 64 96) (by rw [o₉.get .r12, r12₈])
    (by rw [o₉.wr, wr₈]; exact in_fr s _ (by decide) (by decide)) fun v₁₀ m₁₀ => ?_
  obtain f₁₀ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] v.mem v₁₀.mem := by
    rw [m₁₀.mem, o₉.mem, O₈.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 96) (e := 96) (by decide) (by decide) (by decide))
  obtain r12₁₀ : v₁₀.gpr .r12 = fb s := by rw [m₁₀.gpr, o₉.get .r12, r12₈]
  obtain K₁₀ : Frame [kR s] s.mem v₁₀.mem := fv.trans (f₁₀.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, frame_sub s (by decide)⟩)
  refine wp_ld (a := stackArgAddr s 2) (by rw [r12₁₀, stackArgAddr_fb])
    (by rw [m₁₀.rd, o₉.rd, rd₈]; exact arg_rd hp _ (by decide)) fun v₁₁ o₁₁ e₁₁ => ?_
  rw [arg_frame hp K₁₀ (by decide)] at e₁₁
  refine wp_std (a := fb s + BitVec.ofNat 64 104) (by rw [o₁₁.get .r12, r12₁₀])
    (by rw [o₁₁.wr, m₁₀.wr, o₉.wr, wr₈]; exact in_fr s _ (by decide) (by decide)) fun v₁₂ m₁₂ => ?_
  obtain f₁₂ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] v.mem v₁₂.mem := by
    rw [m₁₂.mem, o₁₁.mem]
    exact f₁₀.writeW (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 104) (e := 96) (by decide) (by decide) (by decide))
  obtain K₁₂ : Frame [kR s] s.mem v₁₂.mem := fv.trans (f₁₂.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, frame_sub s (by decide)⟩)
  obtain r12₁₂ : v₁₂.gpr .r12 = fb s := by rw [m₁₂.gpr, o₁₁.get .r12, r12₁₀]
  obtain rd₁₂ : v₁₂.rd = s.rd := by rw [m₁₂.rd, o₁₁.rd, m₁₀.rd, o₉.rd, rd₈]
  refine wp_ld (a := stackArgAddr s 3) (by rw [r12₁₂, stackArgAddr_fb])
    (by rw [rd₁₂]; exact arg_rd hp _ (by decide)) fun v₁₃ o₁₃ e₁₃ => ?_
  refine wp_ld (a := stackArgAddr s 4) (by rw [o₁₃.get .r12, r12₁₂, stackArgAddr_fb])
    (by rw [o₁₃.rd, rd₁₂]; exact arg_rd hp _ (by decide)) fun v₁₄ o₁₄ e₁₄ => ?_
  refine wp_addi fun v₁₅ o₁₅ e₁₅ => wp_nil ?_
  rw [arg_frame hp K₁₂ (by decide)] at e₁₃
  rw [o₁₃.mem, arg_frame hp K₁₂ (by decide)] at e₁₄
  obtain O₁₅ : Only [.r5, .r6, .r3] v₁₂ v₁₅ := (o₁₃.trans (o₁₄.trans o₁₅)).mono
  obtain g₁₂ : ∀ r, r ∉ [Reg.r0] → v₁₂.gpr r = v₈.gpr r := fun r hr => by
    rw [m₁₂.gpr, o₁₁.gpr r hr, m₁₀.gpr, o₉.gpr r hr]
  have mem₁₅ : v₁₅.mem = v₁₂.mem := O₁₅.mem
  obtain hd : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)], ∀ {e k : Nat}, 112 ≤ e → e + k ≤ frameBytes →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 e, k⟩ r := fun r hr e k h₁ h₂ => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega_using [h₁])) (by unfold frameBytes at h₂; omega_using [h₂]) (by decide)
  refine {
    sp := by rw [O₁₅.sp, m₁₂.sp, o₁₁.sp, m₁₀.sp, o₉.sp, sp₈]
    rd := by rw [O₁₅.rd, rd₁₂]
    wr := by rw [O₁₅.wr, m₁₂.wr, o₁₁.wr, m₁₀.wr, o₉.wr, wr₈]
    r28 := by
      rw [O₁₅.get .r28, g₁₂ .r28 (by decide), o₈.get .r28, o₆.get .r28, o₅.get .r28, o₄.get .r28, o₃.get .r28,
        o₂.get .r28, e₁, gv .r3 (by decide)]
    r29 := by
      rw [O₁₅.get .r29, g₁₂ .r29 (by decide), o₈.get .r29, o₆.get .r29, o₅.get .r29, o₄.get .r29, o₃.get .r29,
        e₂, o₁.get .r4, gv .r4 (by decide)]
    r30 := by
      rw [O₁₅.get .r30, g₁₂ .r30 (by decide), o₈.get .r30, o₆.get .r30, o₅.get .r30, o₄.get .r30, e₃,
        o₂.get .r6, o₁.get .r6, gv .r6 (by decide)]
    r31 := by
      rw [O₁₅.get .r31, g₁₂ .r31 (by decide), o₈.get .r31, o₆.get .r31, o₅.get .r31, e₄, o₃.get .r9,
        o₂.get .r9, o₁.get .r9, gv .r9 (by decide), BitVec.ushiftRight_zero]
    hi := fun r hr => by
      obtain h₁ : r ∉ [Reg.r5, .r6, .r3] := by revert r; decide
      obtain h₂ : r ∉ [Reg.r0] := by revert r; decide
      obtain h₃ : r ∉ [Reg.r28, .r29, .r30, .r31, .r9, .r10, .r4] := by revert r; decide
      obtain h₄ : r ∉ [Reg.r12, .r0, .r11] := by revert r; decide
      rw [O₁₅.gpr r h₁, g₁₂ r h₂, O₈.gpr r h₃, gv r h₄]
    mem := by
      rw [mem₁₅]
      exact K₁₂.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
    sv := by
      rw [mem₁₅]
      exact sv.frame_in saved_offs f₁₂ fun r hr => hd r hr (by decide) (by decide)
    ls := by
      rw [mem₁₅, f₁₂.readW (Region.contains_self _ _) (fun r hr => hd r hr (by decide) (by decide)) (by decide)]
      exact lv
    g3 := by rw [e₁₅, o₁₄.get .r12, o₁₃.get .r12, r12₁₂]
    g4 := by
      rw [O₁₅.get .r4, g₁₂ .r4 (by decide), e₈, o₆.get .r6, o₅.get .r6, o₄.get .r6, o₃.get .r6, o₂.get .r6,
        o₁.get .r6, gv .r6 (by decide)]
    g5 := by rw [o₁₅.get .r5, o₁₄.get .r5, e₁₃]
    g6 := by rw [o₁₅.get .r6, e₁₄]
    g7 := by rw [O₁₅.get .r7, g₁₂ .r7 (by decide), O₈.get .r7, gv .r7 (by decide)]
    g8 := by rw [O₁₅.get .r8, g₁₂ .r8 (by decide), O₈.get .r8, gv .r8 (by decide)]
    g9 := by
      rw [O₁₅.get .r9, g₁₂ .r9 (by decide), o₈.get .r9, o₆.get .r9, e₅, o₄.get .r10, o₃.get .r10,
        o₂.get .r10, o₁.get .r10, gv .r10 (by decide)]
    g10 := by
      rw [O₁₅.get .r10, g₁₂ .r10 (by decide), o₈.get .r10, e₆, o₅.get .r6, o₄.get .r6, o₃.get .r6,
        o₂.get .r6, o₁.get .r6, gv .r6 (by decide)]
    a0 := by
      show v₁₅.mem.readW (stackArgAddr v₁₅ 0) 64 = _
      rw [stackArgAddr_in, O₁₅.sp, m₁₂.sp, o₁₁.sp, m₁₀.sp, o₉.sp, sp₈, mem₁₅, m₁₂.mem, o₁₁.mem,
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), m₁₀.mem,
        Mem.readW_writeW_self64]
      exact e₉
    a1 := by
      show v₁₅.mem.readW (stackArgAddr v₁₅ 1) 64 = _
      rw [stackArgAddr_in, O₁₅.sp, m₁₂.sp, o₁₁.sp, m₁₀.sp, o₉.sp, sp₈, mem₁₅, m₁₂.mem, Mem.readW_writeW_self64,
        e₁₁] }

/-- The values of the modulus `pre` holds, which the result is about. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat)

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (s.gpr .r6).toNat)

/-- `EM₁`, of `k` bytes. -/
abbrev em1R (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .r6).toNat⟩

theorem em1_sub {s : State} (hp : PreR s) : Region.Sub (em1R s) (kR s) :=
  frame_sub s (by have := hp.k2; unfold oEM1 frameBytes; omega_using [this])

theorem pdOk_of {s t : State} (hp : PreR s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .r6) : PdOk t := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hfb := fb_toNat hp.sp1
  obtain hgK : (kR s).Disjoint ⟨s.gpr .r10, (s.gpr .r6).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  obtain hgS : (⟨s.gpr .r10, (s.gpr .r6).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  obtain hsa : stackArgAddr t 0 = fb s + BitVec.ofNat 64 96 := by rw [stackArgAddr_in, ha.sp]
  refine ⟨?hl, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, ha.a0, ha.a1, hsa]
    exact {
      on := hp.kp.sub_left (em1_sub hp)
      oe := hp.ke.sub_left (em1_sub hp)
      oi := hgK.sub_left (em1_sub hp)
      os := hp.ks.sub_left (em1_sub hp)
      oa := Offset.disjoint _ (.inr (by decide)) (by unfold oEM1 frameBytes at *; omega_using [hk2]) (by decide)
      ns := hp.sp.symm
      es := hp.es
      is := hgS
      sa := (hp.ks.sub_left (frame_sub s (by decide))).symm
      wo := by
        show (fb s + BitVec.ofNat 64 oEM1).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM1 frameBytes at *; omega_using [hk2, hfb]
      wn := hp.wp
      we := hp.we
      wi := by have := hp.wg; rwa [hsig] at this
      ws := hp.ws }
  case sp => rw [ha.sp]; unfold frameBytes at hfb; omega_using [hfb]
  case hrd =>
    simp only [pdRd]
    rw [ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, hsa, ha.rd, ha.wr]
    obtain hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (fr s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    obtain hg : (⟨s.gpr .r10, (s.gpr .r6).toNat⟩ : Region) ∈ s.rd := by rw [hp.hrd, ← hsig]; simp
    refine Covers.cons (hm _ (by rw [hp.hrd]; simp)) (Covers.cons (hm _ (by rw [hp.hrd]; simp))
      (Covers.cons (hm _ hg) (Covers.one (in_fr' s _ _ (by decide) (by decide)) |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g3, ha.g4, ha.a0, ha.a1, ha.wr]
    exact Covers.cons (Covers.one (in_fr s _ (by decide) (by unfold oEM1 frameBytes; omega_using [hk2])))
      (Covers.of_mem fun x hx => by
        rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ (by rw [hp.hwr]; simp))
  case hk => rw [ha.g4]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g6, ha.g4]; exact hp.hp
  case h10 => rw [ha.g10, ha.g4]
  case he1 => rw [ha.g8]; exact hp.e1
  case he2 => rw [ha.g8, ha.g4]; exact hp.e2
  case hs => rw [ha.g4, ha.a1]; exact hp.hs

/-- After the call: `RMid`, and `EM₁` written with RSAVP1's result if `pre`
holds the modulus' values. -/
structure AfterCall (s t : State) : Prop extends
    Mid (sR s) s (s.gpr .r3) (s.gpr .r4) (s.gpr .r6) ((s.gpr .r9).setWidth 32 |>.setWidth 64) t where
  res : PreOk s →
    Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r6).toNat ((t.gpr .r3).setWidth 32) (pubOut s)

theorem call_ok {s t : State} (hp : PreR s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .r6) :
    WP isa pubCall t (AfterCall s) := by
  have hk2 := hp.k2
  refine pdCall (pdOk_of hp ha hsig) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g3, ha.g4, ha.a0, ha.a1] at hf
  obtain hfm := ha.toMid.frameMem hp.ks (e := oEM1) (n := (s.gpr .r6).toNat) (by decide)
    (by unfold oEM1 frameBytes; omega_using [hk2]) hf
  have hfr0 : Frame [kR s, sR s] s.mem t.mem := ha.mem
  obtain hgK : (kR s).Disjoint ⟨s.gpr .r10, (s.gpr .r6).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  obtain hgS : (⟨s.gpr .r10, (s.gpr .r6).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  refine { ha.toMid.of (fun r hr => hpres r (by revert r; decide)) hsp' hrd' hwr' hfm.1 hfm.2.1 hfm.2.2 with
    res := fun hc => ?_ }
  obtain hw : Spec.Rsa.wordsAt t.mem (t.gpr .r5) (t.gpr .r6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    rw [ha.g5, ha.g6]; exact words_of_frame hfr0 hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (by rw [ha.g4, Proof.RsaPkcs1Sig.bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g3, ha.g4, ha.g7, ha.g8, ha.g9, bytes_of_frame hfr0 hp.ke hp.es.symm (by have := hp.we; omega_using []),
    bytes_of_frame hfr0 hgK hgS.symm (by omega_using [])] at this
  exact this

end VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

end

end


/-!
# `vg_rsa_pkcs1_recover_precomputed` on PPC64LE: correctness

After the call (`AfterCall`), the status is kept in the frame and `encode`
writes to `EM₂` the encoding of the last `out_len` bytes of `EM₁`. If that
fails, `out` is zeroed and the result is 0; if not, those bytes are copied
to `out`, and `out` and the result are masked with whether the encoding is
`EM₁` and the call succeeded (`afterPub_ok`): if `pre` holds the modulus'
values, recovery by encoding (`Proof.RsaPkcs1Sig.recover_eq_recoverEnc`).
As on AArch64 (`Proof/RsaPkcs1Sig/AArch64/RecPcTail.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes ne_of_disjoint bytesAt_drop)

/-! ## The specification -/

/-- The result and `out`, from the entry state `s`: the octets `recover`
returns, or zeros. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s → ∀ h, Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .r9).setWidth 32).toNat = some h →
    Spec.Rsa.written s'.mem (s.gpr .r3) (s.gpr .r4).toNat ((s'.gpr .r3).setWidth 32)
      (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) h
        (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)))

/-- `EM₁` after the call `t`. -/
abbrev em1 (s t : State) : List Byte := Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r6).toNat

/-- The encoding of `EM₁`'s last `out_len` bytes. -/
def encOut (s t : State) : Option (List Byte) :=
  encodeId ((s.gpr .r9).setWidth 32) ((em1 s t).drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat)) (s.gpr .r6).toNat

/-- `recover`, by encoding, as the call's result gives it. -/
theorem recover_eq {s t : State} (hp : PreR s) (hsig : stackArg s 0 = s.gpr .r6)
    (hres : Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r6).toNat ((t.gpr .r3).setWidth 32)
      (pubOut s)) {h : Spec.RsaPkcs1Sig.Hash} (hh : Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .r9).setWidth 32).toNat = some h) :
    Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) h
        (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat) =
      match pubOut s, encOut s t with
      | some em, some em' => if em = em' then some (em.drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat)) else none
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
    cases he : Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat)) (s.gpr .r6).toNat with
    | none => simp
    | some em' =>
      by_cases e : em = em'
      · subst e; simp
      · rw [ite_eq_right (fun h => e (Option.some.inj h).symm)]
        exact (ite_eq_right e).symm

/-! ## The steps -/

theorem add_ofNat_sub (a : Addr) {k L : Nat} (h : L ≤ k) :
    a + BitVec.ofNat 64 k - BitVec.ofNat 64 L = a + BitVec.ofNat 64 (k - L) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem add_ofNat_ofNat (a : Addr) (d e : Nat) :
    a + BitVec.ofNat 64 d + BitVec.ofNat 64 e = a + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- `valPtr`: `r7 := EM₁ + k - out_len`, from `RMid`. -/
theorem valPtr_ok {s t : State} (hp : PreR s) (hm : RMid s t) (h12 : t.gpr .r12 = fb s) :
    WP isa (.block valPtr) t fun w => Only [.r7] t w ∧
      w.gpr .r7 = fb s + BitVec.ofNat 64 (oEM1 + ((s.gpr .r6).toNat - (s.gpr .r4).toNat)) := by
  obtain hL := hp.len_le; have hk := hp.k1
  refine wp_addi fun w₁ o₁ e₁ => wp_add fun w₂ o₂ e₂ => wp_sub fun w₃ o₃ e₃ => wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, ?_⟩
  obtain e6 : BitVec.ofNat 64 (s.gpr .r6).toNat = s.gpr .r6 := by simp
  obtain e4 : BitVec.ofNat 64 (s.gpr .r4).toNat = s.gpr .r4 := by simp
  rw [e₃, e₂, e₁, o₁.get .r30, o₂.get .r29, o₁.get .r29, hm.r30, hm.r29, h12, ← e6, ← e4, add_ofNat_ofNat,
    add_ofNat_sub _ (by omega_arith),
    show oEM1 + (s.gpr .r6).toNat - (s.gpr .r4).toNat = oEM1 + ((s.gpr .r6).toNat - (s.gpr .r4).toNat) by
      unfold oEM1; omega_arith]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s.gpr .r6).isLt, Nat.mod_eq_of_lt (s.gpr .r4).isLt]

/-- `zeroOut`: zeros to the `n` bytes at `r4 = p`, counted in `r11`, and 0
returned. -/
theorem zeroOut_ok {y : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (h4 : y.gpr .r4 = p)
    (h11 : y.gpr .r11 = BitVec.ofNat 64 n) (hw : ∀ i < n, InRegions y.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa zeroOut y fun z => Keep [.r0, .r4, .r11, .r3] y z ∧
      z.mem = writeBytes y.mem p (List.replicate n 0) ∧ z.gpr .r3 = 0 := by
  unfold zeroOut
  refine WP.seq (wp_li (by decide) fun y₁ o₁ e₁ => wp_nil ?_)
  refine WP.seq (WP.mono (fill_ok (p := p) (n := n) (b := 0) hn hn' (by rw [o₁.get .r4, h4]) (by rw [o₁.get .r11, h11]) (by rw [e₁]; rfl)
    (by rw [o₁.wr]; exact hw)) fun y₂ ⟨k₂, m₂⟩ => ?_)
  unfold ret0
  exact wp_li (by decide) fun y₃ o₃ e₃ => wp_nil ⟨((o₁.keep.trans k₂).trans o₃.keep).mono,
    by rw [o₃.mem, m₂, o₁.mem], by rw [e₃]; rfl⟩

/-- `out` is writable in the frame. -/
theorem out_wr {s : State} (hp : PreR s) {i : Nat} (hi : i < (s.gpr .r4).toNat) :
    InRegions (fr s :: s.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 :=
  ⟨oR s, List.mem_cons_of_mem _ (by rw [hp.hwr]; simp),
    Offset.contains_base _ (by omega_arith) (by have := hp.wo; omega_arith)⟩

theorem bytes_written {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hl : xs.length = n) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) q n = xs := by
  subst hl; exact bytesAt_writeBytes _ _ _ hn

theorem ofNat_r4 (s : State) : s.gpr .r4 = BitVec.ofNat 64 (s.gpr .r4).toNat := by simp

/-- Writes of `out` keep `Saves`. -/
theorem saves_out {s y z : State} {rs : List Reg} (hp : PreR s) (h : Saves s y) (o : Keep rs y z) {xs : List Byte}
    (hl : xs.length = (s.gpr .r4).toNat) (hm : z.mem = writeBytes y.mem (s.gpr .r3) xs)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Saves s z :=
  h.keep o (R := [oR s]) (by have := frame_writeBytes y.mem (s.gpr .r3) xs; rw [hl] at this; rw [hm]; exact this)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ko) hrs

/-- The zeros of `zeroKept`, from `RMid`. -/
theorem zeroKept_ok {s w : State} (hp : PreR s) (hm : RMid s w) :
    WP isa zeroKept w fun z => Saves s z ∧ z.gpr .r3 = 0 ∧
      Spec.Rsa.bytesAt z.mem (s.gpr .r3) (s.gpr .r4).toNat = List.replicate (s.gpr .r4).toNat 0 := by
  obtain hL1 := hp.len_pos; have hL2 := hp.len_le
  unfold zeroKept
  refine WP.seq (wp_mov fun y₁ p₁ f₁ => wp_mov fun y₂ p₂ f₂ => wp_nil ?_)
  obtain O₂ : Only [.r4, .r11] w y₂ := p₁.trans p₂
  refine WP.mono (zeroOut_ok (p := s.gpr .r3) (n := (s.gpr .r4).toNat) hL1 (by omega_arith)
    (by rw [p₂.get .r4, f₁, hm.r28]) (by rw [f₂, p₁.get .r29, hm.r29, ← ofNat_r4])
    (fun i hi => by rw [O₂.wr, hm.wr]; exact out_wr hp hi)) fun z ⟨kz, mz, rz⟩ => ⟨?_, rz, ?_⟩
  · exact saves_out hp (hm.only O₂).saves kz (by simp) mz
  · rw [mz, bytes_written (by simp) (by omega_arith)]

/-- The hash value's place in `EM₁`. -/
abbrev dig (s : State) : Addr := fb s + BitVec.ofNat 64 (oEM1 + ((s.gpr .r6).toNat - (s.gpr .r4).toNat))

/-- The hash value's place is in the frame. -/
theorem dig_in {s : State} (hp : PreR s) (rd rs : List Region) {j : Nat} (hj : j < (s.gpr .r4).toNat) :
    InRegions (rd ++ fr s :: rs) (dig s + BitVec.ofNat 64 j) 1 := by
  have := hp.k1; have := hp.k2; have := hp.len_le
  rw [add_ofNat_ofNat]; exact in_fr' s _ _ (by unfold oEM1; omega_arith) (by unfold oEM1 frameBytes; omega_arith)

theorem dig_sub {s : State} (hp : PreR s) : Region.Sub ⟨dig s, (s.gpr .r4).toNat⟩ (kR s) := by
  have := hp.k1; have := hp.k2; have := hp.len_le
  exact frame_sub s (by unfold oEM1 frameBytes; omega_arith)

/-- After the comparison, its difference in `r7`: `out` gets the hash
value's bytes `D` if they encode to `EM₁` and the call succeeded (its status
`st`), zeros if not, and the result says which. -/
theorem release_ok {s y : State} {st : BitVec 64} {D : List Byte} (hp : PreR s) (hm : RMid s y)
    (hst : y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = st)
    (hD : Spec.Rsa.bytesAt y.mem (dig s) (s.gpr .r4).toNat = D) (hlt : (y.gpr .r7).toNat < 256) :
    WP isa release y fun x => Saves s x ∧
      (x.gpr .r3).setWidth 32 = (if y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0 then 1 else 0) ∧
      Spec.Rsa.bytesAt x.mem (s.gpr .r3) (s.gpr .r4).toNat =
        if y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0 then D else List.replicate (s.gpr .r4).toNat 0 := by
  obtain hk1 := hp.k1; have hk2 := hp.k2; have hL1 := hp.len_pos; have hL2 := hp.len_le
  obtain hDl : D.length = (s.gpr .r4).toNat := by rw [← hD, bytesAt_length]
  unfold release maskM
  refine WP.seq (wp_subi fun z₁ q₁ g₁ => wp_lsr fun z₂ q₂ g₂ => wp_addSp fun z₃ q₃ g₃ => ?_)
  rw [q₂.sp, q₁.sp, hm.sp, BitVec.add_zero] at g₃
  refine wp_ld (a := fb s + BitVec.ofNat 64 oSt) (by rw [g₃])
    (by rw [q₃.rd, q₂.rd, q₁.rd, q₃.wr, q₂.wr, q₁.wr, hm.wr]; exact in_fr' s _ _ (by decide) (by decide))
    fun z₄ q₄ g₄ => ?_
  refine wp_lsl fun z₅ q₅ g₅ => wp_lsr fun z₆ q₆ g₆ => wp_li (by decide) fun z₇ q₇ g₇ =>
    wp_sub fun z₈ q₈ g₈ => wp_lsr fun z₉ q₉ g₉ => wp_and fun z₁₀ q₁₀ g₁₀ => wp_sub fun z₁₁ q₁₁ g₁₁ => ?_
  obtain Q₃ : Only [.r8, .r12] y z₃ := (q₁.trans (q₂.trans q₃)).mono
  obtain Q₁₁ : Only [.r9, .r10, .r8] z₃ z₁₁ :=
    (q₄.trans (q₅.trans (q₆.trans (q₇.trans (q₈.trans (q₉.trans (q₁₀.trans q₁₁))))))).mono
  obtain M₁₁ : z₁₁.gpr .r8 = maskOf (y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0) := by
    rw [g₁₁, g₁₀, q₁₀.get .r10, q₉.get .r10, q₉.get .r8, g₉, q₈.get .r10, q₈.get .r8, g₈, g₇, q₇.get .r8,
      q₇.get .r9, g₆, q₆.get .r8, g₅, q₅.get .r8, g₄, q₄.get .r8, q₃.get .r8, q₃.mem, q₂.mem, q₁.mem, hst, g₂, g₁]
    exact mask_eq _ _ hlt
  obtain r12₁₁ : z₁₁.gpr .r12 = fb s := by rw [Q₁₁.get .r12, g₃]
  refine wp_std (a := fb s + BitVec.ofNat 64 oMk) (by rw [r12₁₁])
    (by rw [Q₁₁.wr, Q₃.wr, hm.wr]; exact in_fr s _ (by decide) (by decide)) fun z₁₂ m₁₂ => wp_nil ?_
  obtain fr₁₂ : Frame [⟨fb s + BitVec.ofNat 64 oMk, 8⟩] z₁₁.mem z₁₂.mem := by
    rw [m₁₂.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain mid₁₂ : RMid s z₁₂ := ((hm.only Q₃).only Q₁₁).frameW1 m₁₂.keep hp.ks (by decide) (by decide) fr₁₂
  obtain slot₁₂ : z₁₂.mem.readW (fb s + BitVec.ofNat 64 oMk) 64 = maskOf (y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0) := by
    rw [m₁₂.mem, Mem.readW_writeW_self64, M₁₁]
  obtain D₁₂ : Spec.Rsa.bytesAt z₁₂.mem (dig s) (s.gpr .r4).toNat = D := by
    rw [Proof.RsaPkcs1Sig.bytes_apart (R := ⟨dig s, (s.gpr .r4).toNat⟩) fr₁₂
      (Offset.disjoint _ (.inr (by unfold oMk oEM1; omega_arith)) (by unfold oEM1; omega_arith) (by decide)) (by dsimp only; omega_arith),
      Q₁₁.mem, Q₃.mem, hD]
  -- the value to `out`
  refine WP.seq ?_
  unfold copyOut
  refine WP.seq (WP.block_append_iff.mpr (wp_mov fun c₁ r₁ h₁ => wp_mov fun c₂ r₂ h₂ => wp_nil ?_))
  obtain midc₂ : RMid s c₂ := mid₁₂.only (r₁.trans r₂)
  obtain r12c₂ : c₂.gpr .r12 = fb s := by rw [r₂.get .r12, r₁.get .r12, m₁₂.gpr, r12₁₁]
  refine WP.mono (valPtr_ok hp midc₂ r12c₂) fun c₃ ⟨oc₃, ec₃⟩ => ?_
  obtain midc₃ : RMid s c₃ := midc₂.only oc₃
  obtain Dc₃ : Spec.Rsa.bytesAt c₃.mem (dig s) (s.gpr .r4).toNat = D := by rw [oc₃.mem, r₂.mem, r₁.mem]; exact D₁₂
  refine WP.mono (copy_ok (p := s.gpr .r3) (q := dig s) (n := (s.gpr .r4).toNat) hL1 (by omega_arith)
    (by rw [oc₃.get .r4, r₂.get .r4, h₁, mid₁₂.r28]) ec₃
    (by rw [oc₃.get .r8, h₂, r₁.get .r29, mid₁₂.r29, ← ofNat_r4])
    (fun j hj => by rw [midc₃.rd, midc₃.wr]; exact dig_in hp _ _ hj)
    (fun i hi => by rw [midc₃.wr]; exact out_wr hp hi)
    (fun j hj i hi => ne_of_disjoint (hp.ko.sub_left (dig_sub hp)) (by omega_arith) (by omega_arith) hj hi))
    fun c₄ ⟨kc₄, mc₄⟩ => ?_
  obtain svc₄ : Saves s c₄ := saves_out hp midc₃.saves kc₄ (bytesAt_length _ _ _) mc₄
  obtain outc₄ : Spec.Rsa.bytesAt c₄.mem (s.gpr .r3) (s.gpr .r4).toNat = D := by
    rw [mc₄, bytes_written (bytesAt_length _ _ _) (by omega_arith), Dc₃]
  obtain slotc₄ : c₄.mem.readW (fb s + BitVec.ofNat 64 oMk) 64 = maskOf (y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0) := by
    obtain hf := frame_writeBytes c₃.mem (s.gpr .r3) (Spec.Rsa.bytesAt c₃.mem (dig s) (s.gpr .r4).toNat)
    rw [bytesAt_length] at hf
    rw [mc₄, hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.ko.sub_left (frame_sub s (d := oMk) (n := 8) (by decide))) (by decide), oc₃.mem, r₂.mem,
      r₁.mem, slot₁₂]
  -- the mask's registers
  unfold maskArgs
  refine WP.seq (wp_addSp fun d₁ n₁ k₁ => ?_)
  rw [svc₄.sp, BitVec.add_zero] at k₁
  refine wp_ld (a := fb s + BitVec.ofNat 64 oMk) (by rw [k₁])
    (by rw [n₁.rd, n₁.wr, svc₄.wr]; exact in_fr' s _ _ (by decide) (by decide)) fun d₂ n₂ k₂ =>
    wp_mov fun d₃ n₃ k₃ => wp_mov fun d₄ n₄ k₄ => wp_nil ?_
  obtain N₄ : Only [.r12, .r9, .r11, .r8] c₄ d₄ := n₁.trans (n₂.trans (n₃.trans n₄))
  obtain svd₄ : Saves s d₄ := svc₄.keep N₄.keep (R := []) (by rw [N₄.mem]; exact Frame.refl _ _)
    (fun r h => nomatch h)
  obtain r9d₄ : d₄.gpr .r9 = maskOf (y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0) := by
    rw [n₄.get .r9, n₃.get .r9, k₂, n₁.mem, slotc₄]
  refine WP.seq (WP.mono (maskLoop_ok (p := s.gpr .r3) (n := (s.gpr .r4).toNat) hL1 (by omega_arith)
    (by rw [n₄.get .r11, k₃, n₂.get .r28, n₁.get .r28, kc₄.get .r28, midc₃.r28])
    (by rw [k₄, n₃.get .r29, n₂.get .r29, n₁.get .r29, kc₄.get .r29, midc₃.r29, ← ofNat_r4])
    (fun i hi => by rw [svd₄.wr]; exact out_wr hp hi)) fun e₁ ⟨ke₁, me₁⟩ => ?_)
  rw [r9d₄, N₄.mem, outc₄, maskOf_bytes, hDl] at me₁
  unfold fin
  refine wp_li (by decide) fun f₁ p₁ h₁ => wp_and fun f₂ p₂ h₂ => wp_nil ⟨?_, ?_, ?_⟩
  · refine saves_out hp svd₄ (ke₁.trans (p₁.keep.trans p₂.keep)) (xs := if y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0 then
      D else List.replicate (s.gpr .r4).toNat 0) (by split <;> simp [hDl]) (by rw [p₂.mem, p₁.mem, me₁, N₄.mem])
  · rw [h₂, h₁, p₁.get .r9, ke₁.get .r9, r9d₄, maskOf_fin]
  · rw [p₂.mem, p₁.mem, me₁, bytes_written (by split <;> simp [hDl]) (by omega_arith)]

theorem encodeId_length {x : BitVec 32} {H em : List Byte} {k : Nat} (h : encodeId x H k = some em) :
    em.length = k := by
  unfold encodeId at h
  split at h
  · exact Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- After the call: the status kept, the encoding, the value to `out` or
zeros, and the restores. -/
theorem afterPub_ok {s t : State} (hp : PreR s) (hsig : stackArg s 0 = s.gpr .r6) (ha : AfterCall s t) :
    WP isa (.seq (.block encArgs) (.seq encode (.seq tail (.block restore)))) t
      fun w => Post s (freed frameBytes w) := by
  obtain hk1 := hp.k1; have hk2 := hp.k2; have hL1 := hp.len_pos; have hL2 := hp.len_le
  obtain hfin : ∀ y : State, Saves s y → (PreOk s → ∀ h,
      Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .r9).setWidth 32).toNat = some h →
      Spec.Rsa.written y.mem (s.gpr .r3) (s.gpr .r4).toNat ((y.gpr .r3).setWidth 32)
        (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) h
          (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat))) →
      WP isa (.block restore) y fun w => Post s (freed frameBytes w) :=
    fun y hy hw => WP.mono (restore_ok hy) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hc h hh => by
      rw [freed_mem, freed_gpr, hm, h3]; exact hw hc h hh⟩
  unfold encArgs
  refine WP.seq (WP.block_append_iff.mpr (wp_addSp fun u₁ o₁ e₁ => ?_))
  rw [ha.sp, BitVec.add_zero] at e₁
  refine wp_std (a := fb s + BitVec.ofNat 64 oSt) (by rw [e₁])
    (by rw [o₁.wr, ha.wr]; exact in_fr s _ (by decide) (by decide)) fun u₂ m₂ => ?_
  refine wp_addi fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ => wp_mov fun u₆ o₆ e₆ => wp_nil ?_
  obtain fr₂ : Frame [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem u₂.mem := by
    rw [m₂.mem, o₁.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain mid₂ : RMid s u₂ := ha.toMid.frameW1 (o₁.keep.trans m₂.keep) hp.ks (by decide) (by decide) fr₂
  obtain O₆ : Only [.r4, .r5, .r6, .r8] u₂ u₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  obtain mid₆ : RMid s u₆ := mid₂.only O₆
  obtain r12₆ : u₆.gpr .r12 = fb s := by rw [O₆.get .r12, m₂.gpr, e₁]
  refine WP.mono (valPtr_ok hp mid₆ r12₆) fun u₉ ⟨o₉, e₉⟩ => ?_
  obtain mid₉ : RMid s u₉ := mid₆.only o₉
  obtain r4₉ : u₉.gpr .r4 = fb s + BitVec.ofNat 64 oEM2 := by
    rw [o₉.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, e₃, m₂.gpr, e₁]
  obtain r5₉ : u₉.gpr .r5 = s.gpr .r6 := by rw [o₉.get .r5, o₆.get .r5, o₅.get .r5, e₄, o₃.get .r30, mid₂.r30]
  obtain r6₉ : u₉.gpr .r6 = ((s.gpr .r9).setWidth 32).setWidth 64 := by
    rw [o₉.get .r6, o₆.get .r6, e₅, o₄.get .r31, o₃.get .r31, mid₂.r31]
  obtain r8₉ : u₉.gpr .r8 = s.gpr .r4 := by rw [o₉.get .r8, e₆, o₅.get .r29, o₄.get .r29, o₃.get .r29, mid₂.r29]
  obtain slot₂ : u₂.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .r3 := by
    rw [m₂.mem, Mem.readW_writeW_self64, o₁.get .r3]
  obtain em1₂ : Spec.Rsa.bytesAt u₂.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r6).toNat = em1 s t :=
    Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) fr₂
      (Offset.disjoint _ (.inr (by decide)) (by unfold oEM1; omega_arith) (by decide)) (by dsimp only; omega_arith)
  obtain hpre : EPre u₉ ((s.gpr .r9).setWidth 32) (s.gpr .r6).toNat := {
    r6 := by rw [r6₉, lo32_ext]
    hk := by rw [r5₉]
    kle := hk2
    buf := fun i hi => by
      rw [mid₉.wr, r4₉, add_ofNat_ofNat]
      exact in_fr s _ (by unfold oEM2; omega_arith) (by unfold oEM2 frameBytes; omega_arith)
    rd := fun j hj => by
      rw [r8₉] at hj
      rw [mid₉.rd, mid₉.wr, e₉]; exact dig_in hp _ _ hj
    sep := fun j hj i hi => by
      rw [r8₉] at hj
      rw [e₉, r4₉, add_ofNat_ofNat, add_ofNat_ofNat]
      exact Offset.add_ofNat_ne _ (by unfold oEM1; omega_arith) (by unfold oEM2; omega_arith) (by unfold oEM1 oEM2; omega_arith) }
  obtain hD₉ : Spec.Rsa.bytesAt u₉.mem (dig s) (s.gpr .r4).toNat =
      (em1 s t).drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat) := by
    rw [o₉.mem, O₆.mem, dig, ← add_ofNat_ofNat, ← bytesAt_drop, Nat.sub_add_cancel (by omega_arith), em1₂]
  obtain hH : Spec.Rsa.bytesAt u₉.mem (u₉.gpr .r7) (u₉.gpr .r8).toNat =
      (em1 s t).drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat) := by
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
    obtain midw : RMid s w := mid₉.frameW1 hK hp.ks (e := oEM2) (n := 1024) (by decide) (by decide)
      (by rw [hme]; exact Frame.refl _ _)
    refine WP.ite true ((eval_zero w .r3).trans (by rw [h0]; rfl)) (fun _ => WP.mono (zeroKept_ok hp midw)
      fun y ⟨hy, r3y, oy⟩ => hfin y hy fun hc h hh => ?_) (by simp)
    rw [recover_eq hp hsig (ha.res hc) hh, heo, r3y]
    cases pubOut s <;> exact ⟨rfl, oy⟩
  | some em' =>
    rw [heo] at hout
    obtain ⟨h1, hme⟩ := hout
    refine WP.ite false ((eval_zero w .r3).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
    obtain hl' : em'.length = (s.gpr .r6).toNat := encodeId_length heo
    obtain fw : Frame [⟨fb s + BitVec.ofNat 64 oEM2, 1024⟩] u₉.mem w.mem := by
      rw [hme, r4₉]
      exact (frame_writeBytes _ _ _).sub fun r hr => by
        rw [List.mem_singleton.mp hr, hl']; exact ⟨_, List.mem_singleton_self _, Region.sub_prefix hk2⟩
    obtain midw : RMid s w := mid₉.frameW1 hK hp.ks (by decide) (by decide) fw
    obtain slotw : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .r3 := by
      rw [fw.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)) (by decide), o₉.mem, O₆.mem, slot₂]
    obtain hDw : Spec.Rsa.bytesAt w.mem (dig s) (s.gpr .r4).toNat =
        (em1 s t).drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat) := by
      rw [Proof.RsaPkcs1Sig.bytes_apart (R := ⟨dig s, (s.gpr .r4).toNat⟩) fw
        (Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1; omega_arith) (by decide))
        (by dsimp only; omega_arith), hD₉]
    unfold cmpArgs
    refine WP.seq (wp_addSp fun v₁ p₁ f₁ => wp_addi fun v₂ p₂ f₂ => wp_addi fun v₃ p₃ f₃ =>
      wp_mov fun v₄ p₄ f₄ => wp_nil ?_)
    rw [midw.sp, BitVec.add_zero] at f₁
    obtain P₄ : Only [.r12, .r4, .r5, .r6] w v₄ := p₁.trans (p₂.trans (p₃.trans p₄))
    obtain midv : RMid s v₄ := midw.only P₄
    obtain x4 : v₄.gpr .r4 = fb s + BitVec.ofNat 64 oEM1 := by rw [p₄.get .r4, p₃.get .r4, f₂, f₁]
    obtain x5 : v₄.gpr .r5 = fb s + BitVec.ofNat 64 oEM2 := by rw [p₄.get .r5, f₃, p₂.get .r12, f₁]
    obtain x6 : v₄.gpr .r6 = BitVec.ofNat 64 (s.gpr .r6).toNat := by
      rw [f₄, p₃.get .r30, p₂.get .r30, p₁.get .r30, midw.r30]; simp
    obtain hin : ∀ {d : Nat}, 32 ≤ d → d + (s.gpr .r6).toNat ≤ frameBytes → ∀ j < (s.gpr .r6).toNat,
        InRegions (v₄.rd ++ v₄.wr) (fb s + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 := fun h₀ hd j hj => by
      rw [midv.wr, add_ofNat_ofNat]
      exact in_fr' s _ _ (by omega_arith) (by omega_arith)
    refine WP.seq (WP.mono (compare_ok (s := v₄) (n := (s.gpr .r6).toNat) (by omega_arith) (by omega_arith) x6
      (fun j hj => by rw [x4]; exact hin (by decide) (by unfold oEM1 frameBytes; omega_arith) j hj)
      (fun j hj => by rw [x5]; exact hin (by decide) (by unfold oEM2 frameBytes; omega_arith) j hj))
      fun y ⟨oy, hiff, hlt⟩ => ?_)
    obtain midy : RMid s y := midv.only oy
    obtain hb1 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r6).toNat = em1 s t := by
      rw [P₄.mem, hme, r4₉, o₉.mem, O₆.mem, ← em1₂]
      refine Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) (frame_writeBytes _ _ _) ?_ (by dsimp only; omega_arith)
      rw [hl']
      exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1; omega_arith) (by unfold oEM2; omega_arith)
    obtain hb2 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .r6).toNat = em' := by
      rw [P₄.mem, hme, r4₉, bytes_written hl' (by omega_arith)]
    rw [x4, x5, hb1, hb2] at hiff
    refine WP.mono (release_ok (st := t.gpr .r3)
      (D := (em1 s t).drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat)) hp midy (by rw [oy.mem, P₄.mem, slotw])
      (by rw [oy.mem, P₄.mem, hDw]) hlt) fun x ⟨hx, r3x, outx⟩ => hfin x hx fun hc h hh => ?_
    rw [recover_eq hp hsig (ha.res hc) hh, heo]
    obtain hres := ha.res hc
    cases hpo : pubOut s with
    | none =>
      rw [hpo] at hres
      obtain hc' : ¬ (y.gpr .r7 = 0 ∧ (t.gpr .r3).setWidth 32 ≠ 0) := fun h => h.2 hres.1
      rw [ite_eq_right hc'] at r3x outx
      exact ⟨r3x, outx⟩
    | some em =>
      rw [hpo] at hres
      have he1 : em1 s t = em := hres.2
      dsimp only
      by_cases e : em = em'
      · have hc' : y.gpr .r7 = 0 ∧ (t.gpr .r3).setWidth 32 ≠ 0 :=
          ⟨hiff.mpr (by rw [he1]; exact e), by rw [hres.1]; decide⟩
        rw [ite_eq_left hc'] at r3x outx
        rw [ite_eq_left e]
        exact ⟨r3x, by rw [outx, he1]⟩
      · have hc' : ¬ (y.gpr .r7 = 0 ∧ (t.gpr .r3).setWidth 32 ≠ 0) := fun h => e (by rw [← he1]; exact hiff.mp h.1)
        rw [ite_eq_right hc'] at r3x outx
        rw [ite_eq_right e]
        exact ⟨r3x, outx⟩

/-! ## The whole function -/

theorem lenCheck_ok {s : State} (hp : PreR s) :
    WP isa (.block lenCheck) s fun t₁ => Only [.r12, .r11] s t₁ ∧ t₁.gpr .r11 = stackArg s 0 - s.gpr .r6 := by
  refine wp_addSp fun t₀ o₀ e₀ => wp_ld (a := stackArgAddr s 0) (by rw [e₀, BitVec.add_zero, stackArgAddr_in])
    (by rw [o₀.rd, o₀.wr]; exact arg_rd hp _ (by decide)) fun t₁ o₁ e₁ =>
    wp_sub fun t₂ o₂ e₂ => wp_nil ⟨(o₀.trans (o₁.trans o₂)).mono, ?_⟩
  rw [e₂, e₁, o₁.get .r6, o₀.get .r6, o₀.mem]; rfl

theorem eval_len {s t : State} (e : t.gpr .r11 = stackArg s 0 - s.gpr .r6) :
    isa.eval (.nonzero .d .r11) t = some (decide (stackArg s 0 ≠ s.gpr .r6)) := by
  rw [eval_nonzero, e, ne_zero_iff, BitVec.toNat_sub]
  have := (stackArg s 0).isLt; have := (s.gpr .r6).isLt
  refine congrArg some (decide_eq_decide.mpr ⟨fun h e => ?_, fun h e => h ?_⟩)
  · rw [e] at h; omega_arith
  · apply BitVec.eq_of_toNat_eq; omega_arith

theorem recover_len {s : State} (h : stackArg s 0 ≠ s.gpr .r6) (hh : Spec.RsaPkcs1Sig.Hash) :
    Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) hh
      (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat) = none := by
  unfold Spec.RsaPkcs1Sig.recover
  rw [bytesAt_length, bytesAt_length, ite_eq_right fun e => h (BitVec.eq_of_toNat_eq e)]

theorem code_ok {s : State} (hp : PreR s) : WP isa code s (Post s) := by
  obtain hL1 := hp.len_pos; have hL2 := hp.len_le
  unfold code
  refine WP.seq (WP.mono (lenCheck_ok hp) fun t₁ ⟨o₁, e₁⟩ => ?_)
  obtain hne := eval_len e₁
  by_cases hsig : stackArg s 0 = s.gpr .r6
  · refine WP.ite false (by rw [hne]; simp [hsig]) (by simp) fun _ => ?_
    refine WP.alloc (by decide) (by rw [o₁.sp]; exact hp.sp1) ?_
    obtain fr₁ : frameR frameBytes t₁ = fr s := by rw [frameR_eq]; unfold fr fb; rw [o₁.sp]
    unfold body
    refine WP.seq (WP.mono (pubArgs_ok hp (by rw [allocated_sp, o₁.sp]) (by rw [allocated_wr, fr₁, o₁.wr])
      (by rw [allocated_rd, o₁.rd])
      (by rw [allocated_mem, o₁.mem, o₁.sp]
          exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s))
      (fun r hr => by
        rw [allocated_gpr]
        exact o₁.gpr r fun h => hr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; exact h.symm))
      (by rw [allocated_lr, o₁.lr])) fun t₂ h₂ => ?_)
    exact WP.seq (WP.mono (call_ok hp h₂ hsig) fun t₃ h₃ => afterPub_ok hp hsig h₃)
  · refine WP.ite true (by rw [hne]; simp [hsig]) (fun _ => ?_) (by simp)
    unfold zeroArgs
    refine WP.seq (wp_mov fun y₁ p₁ f₁ => wp_mov fun y₂ p₂ f₂ => wp_nil ?_)
    obtain O₂ : Only [.r12, .r11, .r11, .r4] s y₂ := o₁.trans (p₁.trans p₂)
    refine WP.mono (zeroOut_ok (p := s.gpr .r3) (n := (s.gpr .r4).toNat) hL1 (by omega_arith)
      (by rw [f₂, p₁.get .r3, o₁.get .r3]) (by rw [p₂.get .r11, f₁, o₁.get .r4, ← ofNat_r4])
      (fun i hi => by
        rw [O₂.wr]
        exact ⟨oR s, by rw [hp.hwr]; simp, Offset.contains_base _ (by omega_arith) (by have := hp.wo; omega_arith)⟩))
      fun w ⟨kw, mw, rw₃⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun _ h _ => ?_⟩
    · exact (O₂.keep.trans kw).gpr r (by revert r; decide)
    · rw [kw.sp, O₂.sp]
    · rw [kw.lr, O₂.lr]
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

end VG.Proof.RsaPkcs1Sig.PPC64LE.Rec
