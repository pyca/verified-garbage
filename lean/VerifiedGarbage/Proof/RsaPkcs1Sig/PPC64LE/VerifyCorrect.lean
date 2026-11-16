module

public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Precomputed
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
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-! ### `RsaPkcs1Sig.PPC64LE.VerifyCall`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.PPC64LE.VerifyPre`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_verify_precomputed` on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreV s`: the shared
contract's precondition (`verifyPrecomputedContract`, with the stack of the
frame, `frameBytes`), by name (`preV_of`). As on AArch64
(`Proof/RsaPkcs1Sig/AArch64/VerifyPre.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Ver

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

/-- The buffers: `n`, `e`, the hash value, the signature and the
precomputed values (the working space, the arguments on the stack and the
stack the function uses are `sR`, `aR` and `kR`). -/
abbrev nR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev dR (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
abbrev gR (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

/-- What the code needs of `verifyPrecomputedContract.pre`, by name: the
buffers are readable or writable, apart from each other where one is written
and from the stack the function uses, and do not wrap around; the lengths
are within bounds. -/
structure PreV (s : State) : Prop where
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 136 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, dR s, gR s, pR s, aR s]
  hwr : s.wr = [sR s]
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  ds : (dR s).Disjoint (sR s)
  gs : (gR s).Disjoint (sR s)
  sp : (sR s).Disjoint (pR s)
  sa : (sR s).Disjoint (aR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kd : (kR s).Disjoint (dR s)
  kg : (kR s).Disjoint (gR s)
  ks : (kR s).Disjoint (sR s)
  kp : (kR s).Disjoint (pR s)
  ka : (kR s).Disjoint (aR s)
  wn : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  we : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  wd : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wg : (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  ws : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r4).toNat
  k2 : (s.gpr .r4).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .r6).toNat
  e2 : (s.gpr .r6).toNat ≤ (s.gpr .r4).toNat
  hs : Spec.Rsa.publicScratchWords (s.gpr .r4).toNat ≤ (stackArg s 2).toNat
  hp : (stackArg s 4).toNat = Spec.Rsa.precomputedWords (s.gpr .r4).toNat

theorem preV_of {s : State} (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pre s) : PreV s := by
  have e : frameBytes = 2223 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, ns, es, ds, gs, sp, sa, kn, ke, kd, kg, ks, kp, ka, wn, we, wd, wg, ws, wp, ⟨k1, k2⟩,
    e1, e2, hs, hp⟩ := h
  exact ⟨sp1, by omega_using [sp2], hrd, hwr, ns, es, ds, gs, sp, sa, kn, ke, kd, kg, ks, kp, ka, wn, we, wd, wg, ws, wp, k1, k2,
    e1, e2, hs, hp⟩

end VG.Proof.RsaPkcs1Sig.PPC64LE.Ver

end

end


/-!
# `vg_rsa_pkcs1_verify_precomputed` on PPC64LE: the call

`pubArgs_ok`: the block before the call saves the caller's registers, keeps
`k`, `hash`, `digest` and `digest_len` in `r28`–`r31`, and sets up the call
of `vg_rsa_public_precomputed_checked` (`AtCall`). `call_ok`: the call writes
RSAVP1's result to `EM₁` if `pre` holds the modulus' values (`AfterCall`).
As on AArch64 (`Proof/RsaPkcs1Sig/AArch64/PrecomputedCorrect.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Ver

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Precomputed

/-- In the frame, `k`, `hash`, `digest` and `digest_len` kept. -/
abbrev VMid (s t : State) : Prop :=
  Mid (sR s) s (s.gpr .r4) ((s.gpr .r7).setWidth 32 |>.setWidth 64) (s.gpr .r8) (s.gpr .r9) t

/-- At the call: the arguments of `vg_rsa_public_precomputed_checked`, `EM₁`,
`n_len`, `pre`, `pre_len`, `e`, `e_len`, `sig` and `n_len`, and on the stack
`scratch` and `scratch_len`. -/
structure AtCall (s t : State) : Prop extends
    Mid (sR s) s (s.gpr .r4) ((s.gpr .r7).setWidth 32 |>.setWidth 64) (s.gpr .r8) (s.gpr .r9) t where
  g3 : t.gpr .r3 = fb s + BitVec.ofNat 64 oEM1
  g4 : t.gpr .r4 = s.gpr .r4
  g5 : t.gpr .r5 = stackArg s 3
  g6 : t.gpr .r6 = stackArg s 4
  g7 : t.gpr .r7 = s.gpr .r5
  g8 : t.gpr .r8 = s.gpr .r6
  g9 : t.gpr .r9 = s.gpr .r10
  g10 : t.gpr .r10 = s.gpr .r4
  a0 : stackArg t 0 = stackArg s 1
  a1 : stackArg t 1 = stackArg s 2

section
variable {s : State}

/-- The stack arguments are readable. -/
theorem arg_rd (hp : PreV s) (rs : List Region) {j : Nat} (hj : j < 5) :
    InRegions (s.rd ++ rs) (stackArgAddr s j) 8 :=
  ⟨aR s, List.mem_append_left _ (by rw [hp.hrd]; simp), in_aR hj⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame (hp : PreV s) {m : Mem} (h : Frame [kR s] s.mem m) {j : Nat} (hj : j < 5) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (in_aR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ka.symm) (by decide)

end

theorem pubArgs_ok {s u : State} (hp : PreV s) (hsp : u.sp = fb s) (hwr : u.wr = fr s :: s.wr)
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
  refine wp_mov fun v₁ o₁ e₁ => wp_lsrw fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ =>
    wp_mov fun v₅ o₅ e₅ => wp_mov fun v₆ o₆ e₆ => wp_mov fun v₇ o₇ e₇ => wp_mov fun v₈ o₈ e₈ => ?_
  obtain O₈ : Only [.r28, .r29, .r30, .r31, .r9, .r10, .r7, .r8] v v₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))))).mono
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
      rw [O₁₅.get .r28, g₁₂ .r28 (by decide), o₈.get .r28, o₇.get .r28, o₆.get .r28, o₅.get .r28, o₄.get .r28,
        o₃.get .r28, o₂.get .r28, e₁, gv .r4 (by decide)]
    r29 := by
      rw [O₁₅.get .r29, g₁₂ .r29 (by decide), o₈.get .r29, o₇.get .r29, o₆.get .r29, o₅.get .r29, o₄.get .r29,
        o₃.get .r29, e₂, o₁.get .r7, gv .r7 (by decide),
        BitVec.ushiftRight_zero]
    r30 := by
      rw [O₁₅.get .r30, g₁₂ .r30 (by decide), o₈.get .r30, o₇.get .r30, o₆.get .r30, o₅.get .r30, o₄.get .r30,
        e₃, o₂.get .r8, o₁.get .r8, gv .r8 (by decide)]
    r31 := by
      rw [O₁₅.get .r31, g₁₂ .r31 (by decide), o₈.get .r31, o₇.get .r31, o₆.get .r31, o₅.get .r31, e₄,
        o₃.get .r9, o₂.get .r9, o₁.get .r9, gv .r9 (by decide)]
    hi := fun r hr => by
      obtain h₁ : r ∉ [Reg.r5, .r6, .r3] := by revert r; decide
      obtain h₂ : r ∉ [Reg.r0] := by revert r; decide
      obtain h₃ : r ∉ [Reg.r28, .r29, .r30, .r31, .r9, .r10, .r7, .r8] := by revert r; decide
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
      rw [O₁₅.get .r4, g₁₂ .r4 (by decide), O₈.get .r4, gv .r4 (by decide)]
    g5 := by rw [o₁₅.get .r5, o₁₄.get .r5, e₁₃]
    g6 := by rw [o₁₅.get .r6, e₁₄]
    g7 := by
      rw [O₁₅.get .r7, g₁₂ .r7 (by decide), o₈.get .r7, e₇, o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5,
        o₂.get .r5, o₁.get .r5, gv .r5 (by decide)]
    g8 := by
      rw [O₁₅.get .r8, g₁₂ .r8 (by decide), e₈, o₇.get .r6, o₆.get .r6, o₅.get .r6, o₄.get .r6, o₃.get .r6,
        o₂.get .r6, o₁.get .r6, gv .r6 (by decide)]
    g9 := by
      rw [O₁₅.get .r9, g₁₂ .r9 (by decide), o₈.get .r9, o₇.get .r9, o₆.get .r9, e₅, o₄.get .r10, o₃.get .r10,
        o₂.get .r10, o₁.get .r10, gv .r10 (by decide)]
    g10 := by
      rw [O₁₅.get .r10, g₁₂ .r10 (by decide), o₈.get .r10, o₇.get .r10, e₆, o₅.get .r4, o₄.get .r4,
        o₃.get .r4, o₂.get .r4, o₁.get .r4, gv .r4 (by decide)]
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
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat)

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (s.gpr .r4).toNat)

/-- `EM₁`, of `k` bytes. -/
abbrev em1R (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .r4).toNat⟩

theorem em1_sub {s : State} (hp : PreV s) : Region.Sub (em1R s) (kR s) :=
  frame_sub s (by have := hp.k2; unfold oEM1 frameBytes; omega_using [this])

theorem pdOk_of {s t : State} (hp : PreV s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .r4) : PdOk t := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hfb := fb_toNat hp.sp1
  obtain hgK : (kR s).Disjoint ⟨s.gpr .r10, (s.gpr .r4).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  obtain hgS : (⟨s.gpr .r10, (s.gpr .r4).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
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
        show (fb s + BitVec.ofNat 64 oEM1).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
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
    obtain hg : (⟨s.gpr .r10, (s.gpr .r4).toNat⟩ : Region) ∈ s.rd := by rw [hp.hrd, ← hsig]; simp
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

/-- After the call: `VMid`, and `EM₁` written with RSAVP1's result if `pre`
holds the modulus' values. -/
structure AfterCall (s t : State) : Prop extends
    Mid (sR s) s (s.gpr .r4) ((s.gpr .r7).setWidth 32 |>.setWidth 64) (s.gpr .r8) (s.gpr .r9) t where
  res : PreOk s →
    Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r4).toNat ((t.gpr .r3).setWidth 32) (pubOut s)

theorem call_ok {s t : State} (hp : PreV s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .r4) :
    WP isa pubCall t (AfterCall s) := by
  have hk2 := hp.k2
  refine pdCall (pdOk_of hp ha hsig) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g3, ha.g4, ha.a0, ha.a1] at hf
  obtain hfm := ha.toMid.frameMem hp.ks (e := oEM1) (n := (s.gpr .r4).toNat) (by decide)
    (by unfold oEM1 frameBytes; omega_using [hk2]) hf
  have hfr0 : Frame [kR s, sR s] s.mem t.mem := ha.mem
  obtain hgK : (kR s).Disjoint ⟨s.gpr .r10, (s.gpr .r4).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  obtain hgS : (⟨s.gpr .r10, (s.gpr .r4).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  refine { ha.toMid.of (fun r hr => hpres r (by revert r; decide)) hsp' hrd' hwr' hfm.1 hfm.2.1 hfm.2.2 with
    res := fun hc => ?_ }
  obtain hw : Spec.Rsa.wordsAt t.mem (t.gpr .r5) (t.gpr .r6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    rw [ha.g5, ha.g6]; exact words_of_frame hfr0 hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
    (by rw [ha.g4, Proof.RsaPkcs1Sig.bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g3, ha.g4, ha.g7, ha.g8, ha.g9, bytes_of_frame hfr0 hp.ke hp.es.symm (by have := hp.we; omega_using []),
    bytes_of_frame hfr0 hgK hgS.symm (by omega_using [])] at this
  exact this

end VG.Proof.RsaPkcs1Sig.PPC64LE.Ver

end

end


/-!
# `vg_rsa_pkcs1_verify_precomputed` on PPC64LE: correctness

After the call (`AfterCall`), the status is kept in the frame, `encode`
writes the encoding of the hash value to `EM₂`, and the result is whether it
is `EM₁` (`compare`), masked with the status (`afterPub_ok`): if `pre` holds
the modulus' values, RFC 8017 §8.2.2 (`verifyId_true_iff`). As on AArch64
(`Proof/RsaPkcs1Sig/AArch64/PrecomputedCorrect.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Ver

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes ne_of_disjoint)

/-! ## The specification -/

/-- Verification is RFC 8017 §8.2.2: the signature is `k` bytes, RSAVP1
succeeds and its result is the encoding of the hash value. -/
theorem verifyId_true_iff (nB eB H sig : List Byte) (x : BitVec 32) :
    Spec.RsaPkcs1Sig.verifyId nB eB x.toNat H sig = true ↔
      sig.length = nB.length ∧
        ∃ em, Spec.Rsa.publicOpChecked nB eB sig = some em ∧ encodeId x H nB.length = some em := by
  unfold Spec.RsaPkcs1Sig.verifyId encodeId
  cases hid : Spec.RsaPkcs1Sig.Hash.ofId x.toNat with
  | none => simp
  | some h => dsimp only; rw [Proof.RsaPkcs1Sig.verify_true]

/-- What the function returns, from its entry state. -/
def verOut (s : State) : Bool :=
  Spec.RsaPkcs1Sig.verifyId (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) ((s.gpr .r7).setWidth 32).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)

/-- The encoding of the hash value, from the entry state. -/
def encOut (s : State) : Option (List Byte) :=
  encodeId ((s.gpr .r7).setWidth 32) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (s.gpr .r4).toNat

theorem verOut_eq {s : State} (hsig : stackArg s 0 = s.gpr .r4) :
    verOut s = match pubOut s, encOut s with
      | some em, some em' => em == em'
      | _, _ => false := by
  apply Bool.eq_iff_iff.mpr
  rw [verOut, verifyId_true_iff, bytesAt_length, bytesAt_length, hsig]
  unfold pubOut encOut
  cases hp : Spec.Rsa.publicOpChecked _ _ _ <;> cases he : encodeId _ _ _ <;> simp <;> exact eq_comm

theorem verOut_len {s : State} (h : stackArg s 0 ≠ s.gpr .r4) : verOut s = false := by
  apply Bool.eq_false_iff.mpr
  intro hv
  rw [verOut, verifyId_true_iff, bytesAt_length, bytesAt_length] at hv
  exact h (BitVec.eq_of_toNat_eq hv.1)

theorem encodeId_length {x : BitVec 32} {H em : List Byte} {k : Nat} (h : encodeId x H k = some em) :
    em.length = k := by
  unfold encodeId at h
  split at h
  · exact Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-! ## The steps -/

theorem ite01 (c : Prop) [Decidable c] : (if c then (1 : BitVec 64) else 0).setWidth 32 = if c then 1 else 0 := by
  split <;> rfl

theorem ret0_ok (t : State) : WP isa (.block ret0) t fun w => Only [.r3] t w ∧ w.gpr .r3 = 0 :=
  wp_li (by decide) fun w o e => wp_nil ⟨o, by rw [e]; rfl⟩

theorem mask_ok {s y : State} {st : BitVec 64} (b : Bool) (hm : VMid s y)
    (hst : y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = st) (hr : y.gpr .r3 = if b then 1 else 0) :
    WP isa (.seq (.block mask) (.block restore)) y fun w => abiPreserved s (freed frameBytes w) ∧
      w.gpr .r3 = (if b then 1 else 0) &&& st := by
  unfold mask
  refine WP.seq (wp_addSp fun y₁ o₁ e₁ => ?_)
  rw [hm.sp, BitVec.add_zero] at e₁
  refine wp_ld (a := fb s + BitVec.ofNat 64 oSt) (by rw [e₁])
    (by rw [o₁.rd, o₁.wr, hm.wr]; exact in_fr' s _ _ (by decide) (by decide)) fun y₂ o₂ e₂ =>
    wp_and fun y₃ o₃ e₃ => wp_nil ?_
  refine WP.mono (restore_ok (hm.only (o₁.trans (o₂.trans o₃))).saves) fun w ⟨habi, h3, _⟩ => ⟨habi, ?_⟩
  rw [h3, e₃, o₂.get .r3, o₁.get .r3, hr, e₂, o₁.mem, hst]

/-- The result: the padding check's, masked with the status. -/
theorem final_eq {s t : State} (hsig : stackArg s 0 = s.gpr .r4) (b : Bool)
    (hb : b = match encOut s with
      | some em' => Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r4).toNat == em'
      | none => false)
    (hres : Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r4).toNat ((t.gpr .r3).setWidth 32)
      (pubOut s)) :
    ((if b then (1 : BitVec 64) else 0) &&& t.gpr .r3).setWidth 32 = if verOut s then 1 else 0 := by
  rw [BitVec.setWidth_and, ite01, verOut_eq hsig, hb]
  cases hpo : pubOut s with
  | none =>
    rw [hpo] at hres
    rw [hres.1]
    cases encOut s <;> simp
  | some em =>
    rw [hpo] at hres
    rw [hres.1, hres.2]
    cases encOut s with
    | none => simp
    | some em' => by_cases h : em = em' <;> simp [h]

/-- The result of the function, if `pre` holds the modulus' values, and the
calling convention. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s → (s'.gpr .r3).setWidth 32 = if verOut s then 1 else 0)

/-- After the call: the status kept, the padding check, the mask and the
restores. -/
theorem afterPub_ok {s t : State} (hp : PreV s) (hsig : stackArg s 0 = s.gpr .r4) (ha : AfterCall s t) :
    WP isa (.seq (.block encArgs) (.seq encode (.seq tail (.seq (.block mask) (.block restore))))) t
      fun w => Post s (freed frameBytes w) := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  unfold encArgs
  refine WP.seq (wp_addSp fun u₁ o₁ e₁ => ?_)
  rw [ha.sp, BitVec.add_zero] at e₁
  refine wp_std (a := fb s + BitVec.ofNat 64 oSt) (by rw [e₁])
    (by rw [o₁.wr, ha.wr]; exact in_fr s _ (by decide) (by decide)) fun u₂ m₂ => ?_
  refine wp_addi fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ => wp_mov fun u₆ o₆ e₆ =>
    wp_mov fun u₇ o₇ e₇ => wp_nil ?_
  obtain fr₂ : Frame [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem u₂.mem := by
    rw [m₂.mem, o₁.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain mid₂ : VMid s u₂ := ha.toMid.frameW1 (o₁.keep.trans m₂.keep) hp.ks (by decide) (by decide) fr₂
  obtain O₇ : Only [.r4, .r5, .r6, .r7, .r8] u₂ u₇ := (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))).mono
  obtain mid₇ : VMid s u₇ := mid₂.only O₇
  obtain r4₇ : u₇.gpr .r4 = fb s + BitVec.ofNat 64 oEM2 := by
    rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, e₃, m₂.gpr, e₁]
  obtain r5₇ : u₇.gpr .r5 = s.gpr .r4 := by rw [o₇.get .r5, o₆.get .r5, o₅.get .r5, e₄, o₃.get .r28, mid₂.r28]
  obtain r6₇ : u₇.gpr .r6 = ((s.gpr .r7).setWidth 32).setWidth 64 := by rw [o₇.get .r6, o₆.get .r6, e₅, o₄.get .r29, o₃.get .r29, mid₂.r29]
  obtain r7₇ : u₇.gpr .r7 = s.gpr .r8 := by rw [o₇.get .r7, e₆, o₅.get .r30, o₄.get .r30, o₃.get .r30, mid₂.r30]
  obtain r8₇ : u₇.gpr .r8 = s.gpr .r9 := by rw [e₇, o₆.get .r31, o₅.get .r31, o₄.get .r31, o₃.get .r31, mid₂.r31]
  obtain slot₂ : u₂.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .r3 := by
    rw [m₂.mem, Mem.readW_writeW_self64, o₁.get .r3]
  obtain hd1 : (em1R s).Disjoint ⟨fb s + BitVec.ofNat 64 oSt, 8⟩ :=
    Offset.disjoint _ (.inr (by decide)) (by unfold oEM1; omega_arith) (by decide)
  obtain em1₂ : Spec.Rsa.bytesAt u₂.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r4).toNat =
      Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r4).toNat :=
    Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) fr₂ hd1 (by dsimp only; omega_arith)
  obtain hdk : (dR s).Disjoint ⟨fb s + BitVec.ofNat 64 oEM2, (s.gpr .r4).toNat⟩ :=
    (hp.kd.sub_left (frame_sub s (by unfold oEM2 frameBytes; omega_arith))).symm
  obtain hpre : EPre u₇ ((s.gpr .r7).setWidth 32) (s.gpr .r4).toNat := {
    r6 := by rw [r6₇, lo32_ext]
    hk := by rw [r5₇]
    kle := hk2
    buf := fun i hi => by
      rw [mid₇.wr, r4₇, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_fr s _ (by unfold oEM2; omega_arith) (by unfold oEM2 frameBytes; omega_arith)
    rd := fun j hj => by
      rw [r8₇] at hj
      rw [mid₇.rd, r7₇]
      exact ⟨dR s, List.mem_append_left _ (by rw [hp.hrd]; simp),
        Offset.contains_base _ (by omega_arith) (by have := hp.wd; omega_arith)⟩
    sep := fun j hj i hi => by
      rw [r8₇] at hj
      rw [r7₇, r4₇]
      exact ne_of_disjoint hdk (by have := hp.wd; omega_arith) (by omega_arith) hj hi }
  obtain hH : Spec.Rsa.bytesAt u₇.mem (u₇.gpr .r7) (u₇.gpr .r8).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat := by
    rw [r7₇, r8₇, bytes_of_frame mid₇.mem hp.kd hp.ds.symm (by have := hp.wd; omega_arith)]
  refine WP.seq (WP.mono (encode_ok hpre) fun w ⟨hK, hout⟩ => ?_)
  rw [hH] at hout
  change EOut u₇ w (encOut s) at hout
  obtain hfin : ∀ y : State, ∀ b : Bool, VMid s y → y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .r3 →
      y.gpr .r3 = (if b then 1 else 0) →
      (b = match encOut s with
        | some em' => Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r4).toNat == em'
        | none => false) →
      WP isa (.seq (.block mask) (.block restore)) y fun w => Post s (freed frameBytes w) :=
    fun y b hy hst hr hb => WP.mono (mask_ok b hy hst hr) fun w ⟨habi, h3⟩ => ⟨habi, fun hc => by
      rw [freed_gpr, h3]; exact final_eq hsig b hb (ha.res hc)⟩
  refine WP.seq ?_
  unfold tail
  cases heo : encOut s with
  | none =>
    rw [heo] at hout
    obtain ⟨h0, hme⟩ := hout
    refine WP.ite true ((eval_zero w .r3).trans (by rw [h0]; rfl)) (fun _ => WP.mono (ret0_ok w) fun y ⟨o, e⟩ =>
      hfin y false ((mid₇.frameW1 hK hp.ks (e := oEM2) (n := 1024) (by decide) (by decide)
        (by rw [hme]; exact Frame.refl _ _)).only o)
        (by rw [o.mem, hme, O₇.mem, slot₂]) (by rw [e]; rfl) (by rw [heo])) (by simp)
  | some em' =>
    rw [heo] at hout
    obtain ⟨h1, hme⟩ := hout
    refine WP.ite false ((eval_zero w .r3).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
    obtain hl' : em'.length = (s.gpr .r4).toNat := encodeId_length heo
    obtain fw : Frame [⟨fb s + BitVec.ofNat 64 oEM2, 1024⟩] u₇.mem w.mem := by
      rw [hme, r4₇]
      exact (frame_writeBytes _ _ _).sub fun r hr => by
        rw [List.mem_singleton.mp hr, hl']; exact ⟨_, List.mem_singleton_self _, Region.sub_prefix hk2⟩
    obtain midw : VMid s w := mid₇.frameW1 hK hp.ks (by decide) (by decide) fw
    obtain slotw : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .r3 := by
      rw [fw.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)) (by decide), O₇.mem, slot₂]
    unfold cmpArgs
    refine WP.seq (wp_addSp fun v₁ p₁ f₁ => wp_addi fun v₂ p₂ f₂ => wp_addi fun v₃ p₃ f₃ =>
      wp_mov fun v₄ p₄ f₄ => wp_nil ?_)
    rw [midw.sp, BitVec.add_zero] at f₁
    obtain P₄ : Only [.r12, .r4, .r5, .r6] w v₄ := p₁.trans (p₂.trans (p₃.trans p₄))
    obtain midv : VMid s v₄ := midw.only P₄
    obtain x4 : v₄.gpr .r4 = fb s + BitVec.ofNat 64 oEM1 := by rw [p₄.get .r4, p₃.get .r4, f₂, f₁]
    obtain x5 : v₄.gpr .r5 = fb s + BitVec.ofNat 64 oEM2 := by rw [p₄.get .r5, f₃, p₂.get .r12, f₁]
    obtain x6 : v₄.gpr .r6 = BitVec.ofNat 64 (s.gpr .r4).toNat := by
      rw [f₄, p₃.get .r28, p₂.get .r28, p₁.get .r28, midw.r28, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    obtain hin : ∀ {d : Nat}, 32 ≤ d → d + (s.gpr .r4).toNat ≤ frameBytes → ∀ j < (s.gpr .r4).toNat,
        InRegions (v₄.rd ++ v₄.wr) (fb s + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 := fun h₀ hd j hj => by
      rw [midv.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_fr' s _ _ (by omega_arith) (by omega_arith)
    refine WP.seq (WP.mono (compare_ok (s := v₄) (n := (s.gpr .r4).toNat) (by omega_arith) (by omega_arith) x6
      (fun j hj => by rw [x4]; exact hin (by decide) (by unfold oEM1 frameBytes; omega_arith) j hj)
      (fun j hj => by rw [x5]; exact hin (by decide) (by unfold oEM2 frameBytes; omega_arith) j hj))
      fun y ⟨oy, hiff, hlt⟩ => ?_)
    unfold result
    refine wp_subi fun z₁ q₁ g₁ => wp_lsr fun z₂ q₂ g₂ => wp_nil ?_
    obtain hb1 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r4).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r4).toNat := by
      rw [P₄.mem, hme, r4₇, O₇.mem, ← em1₂]
      refine Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) (frame_writeBytes _ _ _) ?_ (by dsimp only; omega_arith)
      rw [hl']
      exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1; omega_arith) (by unfold oEM2; omega_arith)
    obtain hb2 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .r4).toNat = em' := by
      rw [P₄.mem, hme, r4₇, ← hl', bytesAt_writeBytes _ _ _ (by omega_arith)]
    rw [x4, x5, hb1, hb2] at hiff
    refine hfin z₂ (Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r4).toNat == em')
      (((midv.only oy).only q₁).only q₂) (by rw [q₂.mem, q₁.mem, oy.mem, P₄.mem, slotw]) ?_ (by rw [heo])
    rw [g₂, g₁, borrow1 hlt]
    by_cases h : y.gpr .r7 = 0
    · rw [ite_eq_left h, ite_eq_left (beq_iff_eq.mpr (hiff.mp h))]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr (beq_iff_eq.mp h')))]

/-! ## The whole function -/

theorem lenCheck_ok {s : State} (hp : PreV s) :
    WP isa (.block lenCheck) s fun t₁ => Only [.r12, .r11] s t₁ ∧ t₁.gpr .r11 = stackArg s 0 - s.gpr .r4 := by
  refine wp_addSp fun t₀ o₀ e₀ => wp_ld (a := stackArgAddr s 0) (by rw [e₀, BitVec.add_zero, stackArgAddr_in])
    (by rw [o₀.rd, o₀.wr]; exact arg_rd hp _ (by decide)) fun t₁ o₁ e₁ =>
    wp_sub fun t₂ o₂ e₂ => wp_nil ⟨(o₀.trans (o₁.trans o₂)).mono, ?_⟩
  rw [e₂, e₁, o₁.get .r4, o₀.get .r4, o₀.mem]; rfl

theorem eval_len {s t : State} (e : t.gpr .r11 = stackArg s 0 - s.gpr .r4) :
    isa.eval (.nonzero .d .r11) t = some (decide (stackArg s 0 ≠ s.gpr .r4)) := by
  rw [eval_nonzero, e, ne_zero_iff, BitVec.toNat_sub]
  have := (stackArg s 0).isLt; have := (s.gpr .r4).isLt
  refine congrArg some (decide_eq_decide.mpr ⟨fun h e => ?_, fun h e => h ?_⟩)
  · rw [e] at h; omega_arith
  · apply BitVec.eq_of_toNat_eq; omega_arith

theorem code_ok {s : State} (hp : PreV s) : WP isa code s (Post s) := by
  unfold code
  refine WP.seq (WP.mono (lenCheck_ok hp) fun t₁ ⟨o₁, e₁⟩ => ?_)
  obtain hne := eval_len e₁
  by_cases hsig : stackArg s 0 = s.gpr .r4
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
  · refine WP.ite true (by rw [hne]; simp [hsig]) (fun _ => WP.mono (ret0_ok t₁) fun w ⟨o, e⟩ =>
      ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun _ => ?_⟩) (by simp)
    · exact (o₁.trans o).gpr r (by revert r; decide)
    · rw [o.sp, o₁.sp]
    · rw [o.lr, o₁.lr]
    · rw [e, verOut_len hsig]; rfl

/-- The correctness of `vg_rsa_pkcs1_verify_precomputed`, against its
shared contract. -/
theorem code_correct (s : State) (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok (preV_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  exact hr

end VG.Proof.RsaPkcs1Sig.PPC64LE.Ver
