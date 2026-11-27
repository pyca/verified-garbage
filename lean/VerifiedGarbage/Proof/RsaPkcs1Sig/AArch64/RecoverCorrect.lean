module

public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame
public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Recover
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCall

/-! ### `RsaPkcs1Sig.AArch64.RecoverCall`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Sig.AArch64.RecoverFrame`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.AArch64.RecoverPre`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_recover` on AArch64: the precondition

`PreR K s`: the shared contract's precondition (`recoverContract`, with the
stack `stk K` of `vg_rsa_pkcs1_verify`'s frame, which recovery shares, and
a callee using `K` bytes), by name.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Verify
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk stackArgs_three sR aR kR fb kb stackArgAddr_eq keep_of_frame)

/-- The buffers: `out`, `n`, `e` and the signature (the working space, the
arguments on the stack and the stack used are `vg_rsa_pkcs1_verify`'s). -/
abbrev oR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
abbrev gR (s : State) : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩

/-- What the code needs of `recoverContract.pre`, by name. -/
structure PreR (K : Nat) (s : State) : Prop where
  sp1 : stk K ≤ s.sp.toNat
  sp2 : s.sp.toNat + 24 ≤ 2 ^ 64
  hrd : Covers [nR s, eR s, gR s, aR s] s.rd
  hwo : oR s ∈ s.wr
  hws : sR s ∈ s.wr
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  og : (oR s).Disjoint (gR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  gs : (gR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR s)
  ko : (kR K s).Disjoint (oR s)
  kn : (kR K s).Disjoint (nR s)
  ke : (kR K s).Disjoint (eR s)
  kg : (kR K s).Disjoint (gR s)
  ks : (kR K s).Disjoint (sR s)
  ka : (kR K s).Disjoint (aR s)
  wo : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  wn : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  we : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64
  wg : (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  ws : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .x3).toNat
  k2 : (s.gpr .x3).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .x5).toNat
  e2 : (s.gpr .x5).toNat ≤ (s.gpr .x3).toNat
  hh : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h ∧ (s.gpr .x1).toNat = h.len
  hs : Spec.Rsa.publicScratchWords (s.gpr .x3).toNat ≤ (stackArg s 2).toNat

/-- The length of the hash value is at most `k`, and not 0. -/
theorem hlen {K : Nat} {s : State} (hp : PreR K s) :
    0 < (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ (s.gpr .x3).toNat := by
  obtain ⟨h, -, e⟩ := hp.hh
  have := hp.k1
  rw [e]; cases h <;> simp [Spec.RsaPkcs1Sig.Hash.len] <;> omega_using [this]

theorem kb_toNat {K : Nat} {s : State} (hp : PreR K s) :
    (kb K s).toNat + stk K = s.sp.toNat ∧ s.sp.toNat + 24 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor <;> omega_arith

theorem fb_toNat {K : Nat} {s : State} (hp : PreR K s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stk at this; omega_using [this]

/-- The stack arguments are readable. -/
theorem arg_in {K : Nat} {s : State} (hp : PreR K s) {rs : List Region} (hrd : Covers s.rd rs) {j : Nat}
    (hj : j < 3) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hp.hrd _ _ ⟨aR s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame {K : Nat} {s : State} (hp : PreR K s) {m : Mem} (h : Frame [⟨fb s, frameBytes⟩] s.mem m)
    {j : Nat} (hj : j < 3) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
    (keep_of_frame hp.ka) (by decide)

end VG.Proof.RsaPkcs1Sig.AArch64.Rec

end

end


/-!
# `vg_rsa_pkcs1_recover` on AArch64: the call's arguments

`pubArgs_ok`: the first block saves the registers, keeps `out`, `out_len`,
`k` and `hash` in `x19`–`x22`, and sets up the call (`AtCall`), in
`vg_rsa_pkcs1_verify`'s frame.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Recover
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved save copyArg)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (fb wr_frame in_frame in_frame0 contains_fb saved_offs saved_ho Saved.congr
  Saved.write stackArgAddr_fb)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov wp_movw)

/-- At the call: the registers saved in their slots, `out`, `out_len`, `k`
and `hash` kept in `x19`–`x22`, and the arguments of
`vg_rsa_public_checked` set up. -/
structure AtCall (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x0 : t.gpr .x0 = fb s + BitVec.ofNat 64 oEM1
  x1 : t.gpr .x1 = s.gpr .x3
  x2 : t.gpr .x2 = s.gpr .x2
  x3 : t.gpr .x3 = s.gpr .x3
  x4 : t.gpr .x4 = s.gpr .x4
  x5 : t.gpr .x5 = s.gpr .x5
  x6 : t.gpr .x6 = s.gpr .x7
  x7 : t.gpr .x7 = s.gpr .x3
  x19 : t.gpr .x19 = s.gpr .x0
  x20 : t.gpr .x20 = s.gpr .x1
  x21 : t.gpr .x21 = s.gpr .x3
  x22 : t.gpr .x22 = ((s.gpr .x6).setWidth 32).setWidth 64
  hi : ∀ r ∈ [Reg.x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  a0 : stackArg t 0 = stackArg s 1
  a1 : stackArg t 1 = stackArg s 2

theorem pubArgs_ok {K : Nat} {s u : State} (hp : PreR K s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, r ≠ .x8 → u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block pubArgs) u (AtCall s) := by
  unfold pubArgs save
  simp only [List.cons_append, List.append_assoc]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  obtain hin : ∀ p ∈ saved, InRegions u₁.wr (u₁.gpr .x16 + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [e₁, o₁.wr]; exact wr_frame hwr (by have := saved_offs p hp'; unfold frameBytes; omega_using [this])
  refine Spill.save_ok (b := .x16) (l := saved) saved_ho hin ?_
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : State, u₂ = { u₁ with mem := Spill.saveMem u₁.mem (u₁.gpr .x16) u₁.gpr saved } :=
    ⟨_, rfl⟩
  rw [← hu₂]
  obtain m₂ : Frame [⟨fb s, frameBytes⟩] s.mem u₂.mem := by
    rw [hu₂, e₁, o₁.mem, hm]
    exact Spill.saveMem_frame_base (fun p hp' => by have := saved_offs p hp'; unfold frameBytes; omega_using [this])
      (by decide) _ _ _
  obtain sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [hu₂, e₁]
    refine Saved.congr (Spill.saveMem_saved (by decide) _ _ _) fun p hp' => ?_
    have : p.1 ≠ .x16 ∧ p.1 ≠ .x8 := by revert p; decide
    rw [o₁.get p.1 (by simpa using this.1), hg _ this.2]
  simp only [List.nil_append, copyArg, List.cons_append]
  refine wp_mov fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ => wp_movw fun u₆ o₆ e₆ => ?_
  obtain O₆ : Only [.x19, .x20, .x21, .x22] u₂ u₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  obtain sp₆ : u₆.sp = fb s := by rw [O₆.sp, hu₂]; show u₁.sp = _; rw [o₁.sp, hsp]
  obtain rd₆ : u₆.rd = s.rd := by rw [O₆.rd, hu₂]; show u₁.rd = _; rw [o₁.rd, hrd]
  obtain wr₆ : u₆.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₆.wr, hu₂]; show u₁.wr = _; rw [o₁.wr, hwr]
  obtain a₁ : u₆.sp + BitVec.ofNat 64 (frameBytes + 8 * 1) = stackArgAddr s 1 := by rw [sp₆, stackArgAddr_fb]
  obtain in₁ : InRegions (u₆.rd ++ u₆.wr) (stackArgAddr s 1) 8 := by
    rw [rd₆]; exact arg_in hp (Covers.left (Covers.refl _)) (by decide)
  refine wp_ldrSp (by decide) (by rw [a₁]; exact in₁) fun u₇ o₇ e₇ => ?_
  rw [a₁, O₆.mem, arg_frame hp m₂ (by decide)] at e₇
  obtain g₂ : ∀ r, u₂.gpr r = u₁.gpr r := fun r => by rw [hu₂]
  obtain x16₇ : u₇.gpr .x16 = fb s := by rw [o₇.get .x16, O₆.get .x16, g₂, e₁]
  refine wp_strx (by decide) (by rw [x16₇, BitVec.add_zero]) (by rw [o₇.wr, wr₆]; exact in_frame0 _ _ (by decide))
    fun u₈ m₈ => ?_
  obtain m₈' : Frame [⟨fb s, frameBytes⟩] s.mem u₈.mem := by
    rw [m₈.mem, o₇.mem, O₆.mem]
    exact m₂.writeW (List.mem_singleton_self _) _ (contains_fb s (by decide))
  obtain a₂ : u₈.sp + BitVec.ofNat 64 (frameBytes + 8 * 2) = stackArgAddr s 2 := by
    rw [m₈.sp, o₇.sp, sp₆, stackArgAddr_fb]
  obtain in₂ : InRegions (u₈.rd ++ u₈.wr) (stackArgAddr s 2) 8 := by
    rw [m₈.rd, o₇.rd, rd₆]; exact arg_in hp (Covers.left (Covers.refl _)) (by decide)
  refine wp_ldrSp (by decide) (by rw [a₂]; exact in₂) fun u₉ o₉ e₉ => ?_
  rw [a₂, arg_frame hp m₈' (by decide)] at e₉
  obtain x16₉ : u₉.gpr .x16 = fb s := by rw [o₉.get .x16, m₈.gpr, x16₇]
  refine wp_strx (by decide) (by rw [x16₉]) (by rw [o₉.wr, m₈.wr, o₇.wr, wr₆]; exact in_frame _ _ (by decide))
    fun u₁₀ m₁₀ => ?_
  refine wp_mov fun u₁₁ o₁₁ e₁₁ => wp_mov fun u₁₂ o₁₂ e₁₂ => wp_mov fun u₁₃ o₁₃ e₁₃ =>
    wp_addSp (by decide) fun u₁₄ o₁₄ e₁₄ => wp_nil ?_
  obtain h₁₀ : ∀ r, r ∉ [Reg.x8, .x16, .x19, .x20, .x21, .x22] → u₁₀.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [m₁₀.gpr, o₉.gpr r (by simpa using hr.1), m₈.gpr, o₇.gpr r (by simpa using hr.1),
      O₆.gpr r (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]), g₂, o₁.gpr r (by simpa using hr.2.1),
      hg r hr.1]
  obtain hO : Only [.x1, .x6, .x7, .x0] u₁₀ u₁₄ := (o₁₁.trans (o₁₂.trans (o₁₃.trans o₁₄))).mono
  obtain k₁₉ : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], u₁₄.gpr r = u₆.gpr r := by
    intro r hr
    have : r ∉ [Reg.x1, .x6, .x7, .x0] ∧ r ≠ .x8 := by revert r; decide
    rw [hO.gpr r this.1, m₁₀.gpr, o₉.gpr r (by simpa using this.2), m₈.gpr, o₇.gpr r (by simpa using this.2)]
  obtain sp₁₀ : u₁₀.sp = fb s := by rw [m₁₀.sp, o₉.sp, m₈.sp, o₇.sp, sp₆]
  obtain u₁₃sp : u₁₃.sp = fb s := by rw [o₁₃.sp, o₁₂.sp, o₁₁.sp, sp₁₀]
  obtain mem₁₀ : u₁₀.mem = (u₈.mem).writeW (fb s + BitVec.ofNat 64 8) (stackArg s 2) := by
    rw [m₁₀.mem, o₉.mem, e₉]
  obtain mem₈ : u₈.mem = (u₂.mem).writeW (fb s) (stackArg s 1) := by
    rw [m₈.mem, o₇.mem, O₆.mem, e₇]
  refine ⟨?sp, ?rd, ?wr, ?x0, ?x1, ?x2, ?x3, ?x4, ?x5, ?x6, ?x7, ?x19, ?x20, ?x21, ?x22, ?hi, ?v, ?mem, ?sv, ?a0,
    ?a1⟩
  case sp => rw [o₁₄.sp, u₁₃sp]
  case rd => rw [hO.rd, m₁₀.rd, o₉.rd, m₈.rd, o₇.rd, rd₆]
  case wr => rw [hO.wr, m₁₀.wr, o₉.wr, m₈.wr, o₇.wr, wr₆]
  case x0 => rw [e₁₄, u₁₃sp]
  case x1 => rw [o₁₄.get .x1, o₁₃.get .x1, o₁₂.get .x1, e₁₁, h₁₀ .x3 (by decide)]
  case x2 => rw [hO.get .x2, h₁₀ .x2 (by decide)]
  case x3 => rw [hO.get .x3, h₁₀ .x3 (by decide)]
  case x4 => rw [hO.get .x4, h₁₀ .x4 (by decide)]
  case x5 => rw [hO.get .x5, h₁₀ .x5 (by decide)]
  case x6 => rw [o₁₄.get .x6, o₁₃.get .x6, e₁₂, o₁₁.get .x7, h₁₀ .x7 (by decide)]
  case x7 => rw [o₁₄.get .x7, e₁₃, o₁₂.get .x3, o₁₁.get .x3, h₁₀ .x3 (by decide)]
  case x19 => rw [k₁₉ .x19 (by decide), o₆.get .x19, o₅.get .x19, o₄.get .x19, e₃, g₂, o₁.get .x0,
    hg .x0 (by decide)]
  case x20 => rw [k₁₉ .x20 (by decide), o₆.get .x20, o₅.get .x20, e₄, o₃.get .x1, g₂, o₁.get .x1,
    hg .x1 (by decide)]
  case x21 => rw [k₁₉ .x21 (by decide), o₆.get .x21, e₅, o₄.get .x3, o₃.get .x3, g₂, o₁.get .x3,
    hg .x3 (by decide)]
  case x22 => rw [k₁₉ .x22 (by decide), e₆, o₅.get .x6, o₄.get .x6, o₃.get .x6, g₂, o₁.get .x6,
    hg .x6 (by decide)]
  case hi =>
    intro r hr
    have : r ∉ [Reg.x1, .x6, .x7, .x0] ∧ r ∉ [Reg.x8, .x16, .x19, .x20, .x21, .x22] := by
      revert r; decide
    rw [hO.gpr r this.1, h₁₀ r this.2]
  case v =>
    intro r hr
    rw [hO.vcs r hr, m₁₀.vcs r hr, o₉.vcs r hr, m₈.vcs r hr, o₇.vcs r hr, O₆.vcs r hr, hu₂]
    show (u₁.v r).extractLsb' 0 64 = _
    rw [o₁.vcs r hr, hv r hr]
  case mem =>
    rw [hO.mem, mem₁₀]
    exact m₈'.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  case sv =>
    rw [hO.mem, mem₁₀, mem₈]
    exact Saved.write (d := 8) (Saved.write (d := 0) (by simpa using sv₂) (by decide) _ |> fun h => by
      simpa using h) (by decide) _
  case a0 =>
    show (u₁₄.mem).readW (u₁₄.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
    rw [o₁₄.sp, u₁₃sp, hO.mem, mem₁₀]
    simp only [Nat.mul_zero, BitVec.add_zero]
    rw [Mem.readW_writeW_sep (Offset.sep_base (fb s) (by decide) (by decide)) (by decide), mem₈]
    exact Mem.readW_writeW_self64 _ _ _
  case a1 =>
    show (u₁₄.mem).readW (u₁₄.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
    rw [o₁₄.sp, u₁₃sp, hO.mem, mem₁₀]
    exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.RsaPkcs1Sig.AArch64.Rec

end

end


/-!
# `vg_rsa_pkcs1_recover` on AArch64: the call of `vg_rsa_public_checked`

RSAVP1 of the signature, as the entry state gives it (`pubOut`); `EM₁` in
the frame (`em1R`, `em1_sub`); and the values in `x19`–`x22` and the saved
slots in the frame (`Mid`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Recover
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk sR aR kR fb kb fb_eq off_fb frame_sub frame_sub0 below_fb in_frame
  in_frame0 saved_offs bytes_of_frame)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)

/-- `EM₁`, of `k` bytes. -/
abbrev em1R (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x3).toNat⟩

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (s.gpr .x3).toNat)

/-- In the frame, from the entry state `s`: the registers saved, `x19`–`x22`
holding `out`, `out_len`, `k` and `hash`. -/
structure Mid (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : t.gpr .x19 = s.gpr .x0
  x20 : t.gpr .x20 = s.gpr .x1
  x21 : t.gpr .x21 = s.gpr .x3
  x22 : t.gpr .x22 = ((s.gpr .x6).setWidth 32).setWidth 64
  hi : ∀ r ∈ [Reg.x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  sv : Spill.Saved (fb s) s.gpr saved t.mem

/-- `EM₁` is in the frame. -/
theorem em1_sub {K : Nat} {s : State} (hp : PreR K s) : Region.Sub (em1R s) (kR K s) :=
  frame_sub K s (by have := hp.k2; unfold oEM1 frameBytes; omega_using [this])

end VG.Proof.RsaPkcs1Sig.AArch64.Rec

end

end

/-!
# `vg_rsa_pkcs1_recover` on AArch64: correctness

Pieces of the proof of correctness: the encoding of the last `out_len`
bytes of `EM₁` into `EM₂` (`encode`, `enc_ok`), the release of those bytes
to `out` (`copyOut_ok`), or zeros (`zeroKept_ok`, `zeroArgs_ok`), the
restores (`restore_ok`), and the result BoringSSL's recovery
(`recover_eq_recoverEnc`) gives, from the entry state (`recover_eq`,
`recover_none`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Recover VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.AArch64 (encode compare psLoop copyLoop)
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved restore)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk sR aR kR fb kb frame_sub in_frame saved_offs saved_ho eval_zero')
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_add wp_sub eval_nonzero ne_zero_iff)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov wp_movw EPre EPost EOut encodeId encode_ok compare_ok
  fill_ok copy_ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes ne_of_disjoint bytesAt_drop
  bytes_apart)

/-! ## `Mid` -/

/-- `Mid` is kept by code that writes only registers other than `x19`–`x28`. -/
theorem Mid.only {s t w : State} {rs : List Reg} (h : Mid s t) (o : Only rs t w)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid s w where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x19
  x20 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x20
  x21 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x21
  x22 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x22
  hi := fun r hr => (o.gpr _ fun h' => hrs _ h' (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h <;> simp [h])).trans (h.hi r hr)
  v := fun r hr => (o.vcs r hr).trans (h.v r hr)
  sv := by rw [o.mem]; exact h.sv

/-- `Mid` is kept by code that writes only registers other than `x19`–`x28`
and memory apart from the saved registers' slots. -/
theorem Mid.frame {s t w : State} {rs : List Reg} {R : Region} (h : Mid s t) (o : Keep rs t w)
    (hm : Frame [R] t.mem w.mem) (hd : Region.Disjoint ⟨fb s + BitVec.ofNat 64 16, 40⟩ R)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid s w :=
  have hw : Mid s { t with gpr := w.gpr, v := w.v } :=
    Mid.only (w := { t with gpr := w.gpr, v := w.v }) h ⟨o.gpr, rfl, rfl, rfl, rfl, o.vcs⟩ hrs
  { hw with
    sp := o.sp.trans h.sp
    rd := o.rd.trans h.rd
    wr := o.wr.trans h.wr
    sv := h.sv.frame_in saved_offs hm fun r hr => by rw [List.mem_singleton.mp hr]; exact hd }

/-- The saved registers' slots are apart from `out`. -/
theorem slots_out {K : Nat} {s : State} (hp : PreR K s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 16, 40⟩ (oR s) :=
  hp.ko.sub_left (frame_sub K s (d := 16) (n := 40) (by decide))

/-- `out` is writable. -/
theorem out_wr {K : Nat} {s : State} (hp : PreR K s) (rs : List Region) :
    ∀ i < (s.gpr .x1).toNat, InRegions (rs ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 i) 1 := fun i hi =>
  ⟨_, List.mem_append_right _ hp.hwo, Offset.contains_base _ (by omega_arith) (by have := hp.wo; omega_arith)⟩

/-! ## Zeros to `out` -/

theorem zeroOut_ok {u : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h14 : u.gpr .x14 = p) (h13 : u.gpr .x13 = BitVec.ofNat 64 n)
    (hw : ∀ i < n, InRegions u.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa zeroOut u fun w => Keep [.x15, .x13, .x14, .x0] u w ∧
      w.mem = writeBytes u.mem p (List.replicate n 0) ∧ w.gpr .x0 = 0 := by
  unfold zeroOut
  refine WP.seq (wp_movz fun u₁ o₁ e₁ => wp_nil ?_)
  refine WP.seq (WP.mono (fill_ok (p := p) (b := 0) hn hn' (by rw [o₁.get .x14, h14]) (by rw [o₁.get .x13, h13])
    (by rw [e₁]; rfl) (by rw [o₁.wr]; exact hw)) fun u₂ ⟨k₂, m₂⟩ => ?_)
  exact wp_movz fun u₃ o₃ e₃ => wp_nil ⟨(o₁.keep.trans (k₂.trans o₃.keep)).mono, by
    rw [o₃.mem, m₂, o₁.mem], by rw [e₃]; rfl⟩

/-- Zeros to `out`, from `Mid`. -/
theorem zeroKept_ok {K : Nat} {s t : State} (hp : PreR K s) (hm : Mid s t) :
    WP isa zeroKept t fun w => Mid s w ∧
      Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat ((w.gpr .x0).setWidth 32) none := by
  obtain ⟨hl0, hl1⟩ := hlen hp
  have := hp.k2
  unfold zeroKept
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_nil ?_)
  have O₂ : Only [.x14, .x13] t u₂ := (o₁.trans o₂).mono
  refine WP.mono (zeroOut_ok (p := s.gpr .x0) (n := (s.gpr .x1).toNat) hl0 (by omega_arith)
    (by rw [o₂.get .x14, e₁, hm.x19]) (by rw [e₂, o₁.get .x20, hm.x20, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [O₂.wr, hm.wr]; exact out_wr hp [_])) fun w ⟨k, mw, x0⟩ => ⟨?_, ?_, ?_⟩
  · refine (hm.only O₂).frame k (R := oR s) (by
      rw [mw]; have := frame_writeBytes u₂.mem (s.gpr .x0) (List.replicate (s.gpr .x1).toNat 0)
      rwa [List.length_replicate] at this) (slots_out hp)
  · rw [x0]; rfl
  · rw [mw]
    have := bytesAt_writeBytes u₂.mem (s.gpr .x0) (List.replicate (s.gpr .x1).toNat 0) (by simp; omega_arith)
    rwa [List.length_replicate] at this

/-! ## The hash value's place in `EM₁` -/

/-- The last `out_len` bytes of `EM₁`. -/
abbrev valA (s : State) : Addr := fb s + BitVec.ofNat 64 (oEM1 + ((s.gpr .x3).toNat - (s.gpr .x1).toNat))

theorem addSub_eq (b x y : BitVec 64) {d : Nat} (h : y.toNat ≤ x.toNat) :
    b + BitVec.ofNat 64 d + x - y = b + BitVec.ofNat 64 (d + (x.toNat - y.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

theorem valPtr_ok {K : Nat} {s u : State} (hp : PreR K s) (hsp : u.sp = fb s) (h21 : u.gpr .x21 = s.gpr .x3)
    (h20 : u.gpr .x20 = s.gpr .x1) :
    WP isa (.block valPtr) u fun u' => Only [.x11] u u' ∧ u'.gpr .x11 = valA s := by
  have := hlen hp; have := hp.k2
  unfold valPtr
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ =>
    wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, ?_⟩
  rw [e₃, e₂, e₁, o₁.get .x21, o₂.get .x20, o₁.get .x20, h21, h20, hsp,
    addSub_eq _ _ _ (by omega_arith)]


theorem valA_eq (s : State) :
    valA s = fb s + BitVec.ofNat 64 oEM1 + BitVec.ofNat 64 ((s.gpr .x3).toNat - (s.gpr .x1).toNat) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem valA_sub {K : Nat} {s : State} (hp : PreR K s) : Region.Sub ⟨valA s, (s.gpr .x1).toNat⟩ (kR K s) :=
  frame_sub K s (by have := hlen hp; have := hp.k2; unfold oEM1 frameBytes; omega_arith)

/-- The last `out_len` bytes of `EM₁`. -/
theorem val_bytes {s : State} {m : Mem} {em : List Byte} (hl : (s.gpr .x1).toNat ≤ (s.gpr .x3).toNat)
    (hem : Spec.Rsa.bytesAt m (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em) :
    Spec.Rsa.bytesAt m (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - (s.gpr .x1).toNat) := by
  rw [← hem, valA_eq, ← bytesAt_drop, Nat.sub_add_cancel hl]

/-- Bytes in the frame are readable. -/
theorem frame_bytes {s u : State} (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) {d n : Nat}
    (h : d + n ≤ frameBytes) :
    ∀ j < n, InRegions (u.rd ++ u.wr) (fb s + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 := fun j hj => by
  rw [hwr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact InRegions_append_cons (xs := u.rd) |>.mpr (.inl (Offset.contains_base _ (by omega_arith)
    (by unfold frameBytes at h; omega_arith)))

/-! ## The release of the hash value -/

theorem copyOut_ok {K : Nat} {s y : State} (hp : PreR K s) (hm : Mid s y) :
    WP isa copyOut y fun w => Mid s w ∧ Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat
      ((w.gpr .x0).setWidth 32) (some (Spec.Rsa.bytesAt y.mem (valA s) (s.gpr .x1).toNat)) ∧
      w.mem = writeBytes y.mem (s.gpr .x0) (Spec.Rsa.bytesAt y.mem (valA s) (s.gpr .x1).toNat) ∧
      w.gpr .x0 = 1 := by
  obtain ⟨hl0, hl1⟩ := hlen hp
  have := hp.k2
  unfold copyOut
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => ?_)
  have O₂ : Only [.x14, .x12] y u₂ := (o₁.trans o₂).mono
  refine WP.mono (valPtr_ok hp (by rw [O₂.sp, hm.sp]) (by rw [O₂.get .x21, hm.x21])
    (by rw [O₂.get .x20, hm.x20])) fun u₃ ⟨o₃, e₃⟩ => ?_
  have O₃ : Only [.x14, .x12, .x11] y u₃ := (O₂.trans o₃).mono
  have hd : (⟨valA s, (s.gpr .x1).toNat⟩ : Region).Disjoint (oR s) := hp.ko.sub_left (valA_sub hp)
  refine WP.seq (WP.mono (copy_ok (p := s.gpr .x0) (q := valA s) (n := (s.gpr .x1).toNat) hl0 (by omega_arith)
    (by rw [o₃.get .x14, o₂.get .x14, e₁, hm.x19]) e₃
    (by rw [o₃.get .x12, e₂, o₁.get .x20, hm.x20, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => frame_bytes (by rw [O₃.wr, hm.wr]) (by unfold oEM1 frameBytes; omega_arith) j hj)
    (by rw [O₃.wr, hm.wr]; exact out_wr hp [_])
    (fun j hj i hi => ne_of_disjoint hd (by omega_arith) (by omega_arith) hj hi)) fun u₄ ⟨k₄, m₄⟩ => ?_)
  refine wp_movz fun u₅ o₅ e₅ => wp_nil ⟨((hm.only O₃).frame k₄ (R := oR s) (by
    rw [m₄]; have := frame_writeBytes u₃.mem (s.gpr .x0) (Spec.Rsa.bytesAt u₃.mem (valA s) (s.gpr .x1).toNat)
    rwa [bytesAt_length] at this) (slots_out hp)).only o₅, ⟨by rw [e₅]; rfl, ?_⟩,
    by rw [o₅.mem, m₄, O₃.mem], by rw [e₅]; rfl⟩
  rw [o₅.mem, m₄, O₃.mem]
  have := bytesAt_writeBytes y.mem (s.gpr .x0) (Spec.Rsa.bytesAt y.mem (valA s) (s.gpr .x1).toNat)
    (by rw [bytesAt_length]; omega_arith)
  rwa [bytesAt_length] at this

/-! ## After the call -/

/-- `vg_rsa_pkcs1_recover`'s result, from the entry state, for the hash
function `h`, if the signature is `k` bytes. -/
def recOut (s : State) (h : Spec.RsaPkcs1Sig.Hash) : Option (List Byte) :=
  match pubOut s with
  | some em =>
    if Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .x3).toNat - h.len)) (s.gpr .x3).toNat = some em then
      some (em.drop ((s.gpr .x3).toNat - h.len))
    else none
  | none => none

theorem encArgs_ok {K : Nat} {s t : State} (hp : PreR K s) (hm : Mid s t) :
    WP isa (.block encArgs) t fun u => Only [.x8, .x9, .x10, .x12, .x11] t u ∧
      u.gpr .x8 = fb s + BitVec.ofNat 64 oEM2 ∧ u.gpr .x9 = s.gpr .x3 ∧
      u.gpr .x10 = ((s.gpr .x6).setWidth 32).setWidth 64 ∧ u.gpr .x12 = s.gpr .x1 ∧ u.gpr .x11 = valA s := by
  unfold encArgs
  rw [WP.block_append_iff]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ =>
    wp_mov fun u₄ o₄ e₄ => wp_nil ?_
  have O₄ : Only [.x8, .x9, .x10, .x12] t u₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine WP.mono (valPtr_ok hp (by rw [O₄.sp, hm.sp]) (by rw [O₄.get .x21, hm.x21]) (by rw [O₄.get .x20, hm.x20]))
    fun u ⟨o, e⟩ => ⟨(O₄.trans o).mono, ?_, ?_, ?_, ?_, e⟩
  · rw [o.get .x8, o₄.get .x8, o₃.get .x8, o₂.get .x8, e₁, hm.sp]
  · rw [o.get .x9, o₄.get .x9, o₃.get .x9, e₂, o₁.get .x21, hm.x21]
  · rw [o.get .x10, o₄.get .x10, e₃, o₂.get .x22, o₁.get .x22, hm.x22]
  · rw [o.get .x12, e₄, o₃.get .x20, o₂.get .x20, o₁.get .x20, hm.x20]

/-- The encoding of the last `h.len` bytes of `em`, with `k` bytes. -/
def encRes (s : State) (h : Spec.RsaPkcs1Sig.Hash) (em : List Byte) : Option (List Byte) :=
  Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .x3).toNat - h.len)) (s.gpr .x3).toNat

/-- Before `encode`, `EM₁` holding `em`. -/
structure AtEnc (s : State) (em : List Byte) (u : State) : Prop where
  mid : Mid s u
  x8 : u.gpr .x8 = fb s + BitVec.ofNat 64 oEM2
  x9 : u.gpr .x9 = s.gpr .x3
  x10 : u.gpr .x10 = ((s.gpr .x6).setWidth 32).setWidth 64
  x12 : u.gpr .x12 = s.gpr .x1
  x11 : u.gpr .x11 = valA s
  em1 : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em

/-- After `encode`: its result, and the buffers. -/
structure AfterEnc (s : State) (h : Spec.RsaPkcs1Sig.Hash) (em : List Byte) (w : State) : Prop where
  mid : Mid s w
  res : match encRes s h em with
    | none => w.gpr .x0 = 0
    | some em' => w.gpr .x0 = 1 ∧ Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em ∧
      Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .x3).toNat = em' ∧
      Spec.Rsa.bytesAt w.mem (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - h.len)

theorem enc_ok {K : Nat} {s u : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash}
    (hh : Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h) (hol : (s.gpr .x1).toNat = h.len)
    {em : List Byte} (hu : AtEnc s em u) :
    WP isa encode u fun w => AfterEnc s h em w ∧ Frame [⟨fb s + BitVec.ofNat 64 oEM2, (s.gpr .x3).toNat⟩] u.mem w.mem := by
  obtain ⟨hl0, hl1⟩ := hlen hp
  have hk1 := hp.k1; have hk2 := hp.k2
  have hval : Spec.Rsa.bytesAt u.mem (u.gpr .x11) (u.gpr .x12).toNat = em.drop ((s.gpr .x3).toNat - h.len) := by
    rw [hu.x11, hu.x12, val_bytes hl1 hu.em1, hol]
  have hpre : EPre u ((s.gpr .x6).setWidth 32) (s.gpr .x3).toNat := {
    x10 := by rw [hu.x10]; simp
    hk := by rw [hu.x9]
    kle := hk2
    buf := fun i hi => by
      rw [hu.mid.wr, hu.x8, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_frame _ _ (by unfold oEM2 frameBytes; omega_arith)
    rd := fun j hj => by
      rw [hu.x11]; rw [hu.x12] at hj
      exact frame_bytes hu.mid.wr (by unfold oEM1 frameBytes; omega_arith) j hj
    sep := fun j hj i hi => by
      rw [hu.x11, hu.x8]; rw [hu.x12] at hj
      exact ne_of_disjoint (Offset.disjoint _ (by unfold oEM1 oEM2; omega_arith) (by unfold oEM1; omega_arith)
        (by unfold oEM2; omega_arith)) (by omega_arith) (by omega_arith) hj hi }
  refine WP.mono (encode_ok hpre) fun w ⟨hK, hout⟩ => ?_
  have henc : encodeId ((s.gpr .x6).setWidth 32) (em.drop ((s.gpr .x3).toNat - h.len)) (s.gpr .x3).toNat =
      encRes s h em := by
    unfold encodeId encRes; rw [hh]
  rw [hval, henc] at hout
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · cases heo : encRes s h em with
    | none =>
      rw [heo] at hout
      exact hu.mid.only (Ver.Only.of_keep hK hout.2)
    | some em' =>
      rw [heo] at hout
      have hl' : em'.length = (s.gpr .x3).toNat := Proof.RsaPkcs1Sig.encode_length heo
      exact hu.mid.frame hK (R := ⟨fb s + BitVec.ofNat 64 oEM2, em'.length⟩) (by rw [hout.2, hu.x8]; exact frame_writeBytes _ _ _)
        (Offset.disjoint _ (by unfold oEM2; omega_arith) (by decide) (by unfold oEM2; omega_arith))
  · cases heo : encRes s h em with
    | none => rw [heo] at hout; exact hout.1
    | some em' =>
      rw [heo] at hout
      obtain ⟨h1, hme⟩ := hout
      have hl' : em'.length = (s.gpr .x3).toNat := Proof.RsaPkcs1Sig.encode_length heo
      have fw : Frame [⟨fb s + BitVec.ofNat 64 oEM2, em'.length⟩] u.mem w.mem := by
        rw [hme, hu.x8]; exact frame_writeBytes _ _ _
      have d1 : (⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x3).toNat⟩ : Region).Disjoint
          ⟨fb s + BitVec.ofNat 64 oEM2, em'.length⟩ := by
        rw [hl']; exact Offset.disjoint _ (by unfold oEM1 oEM2; omega_arith) (by unfold oEM1; omega_arith) (by unfold oEM2; omega_arith)
      have dv : (⟨valA s, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨fb s + BitVec.ofNat 64 oEM2, em'.length⟩ := by
        rw [hl']; exact Offset.disjoint _ (by unfold oEM1 oEM2; omega_arith) (by unfold oEM1; omega_arith) (by unfold oEM2; omega_arith)
      refine ⟨h1, ?_, ?_, ?_⟩
      · rw [← hu.em1]
        exact bytes_apart (R := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x3).toNat⟩) fw d1 (by dsimp only; omega_arith)
      · rw [hme, hu.x8, ← hl', bytesAt_writeBytes _ _ _ (by omega_arith)]
      · rw [← hol, ← val_bytes hl1 hu.em1]
        exact bytes_apart (R := ⟨valA s, (s.gpr .x1).toNat⟩) fw dv (by dsimp only; omega_arith)
  · cases heo : encRes s h em with
    | none =>
      rw [heo] at hout
      rw [(Ver.Only.of_keep hK hout.2).mem]; exact Frame.refl _ _
    | some em' =>
      rw [heo] at hout
      have hl' : em'.length = (s.gpr .x3).toNat := Proof.RsaPkcs1Sig.encode_length heo
      rw [hout.2, hu.x8, ← hl']; exact frame_writeBytes _ _ _

/-- Before `compare`. -/
structure AtCmp (s : State) (h : Spec.RsaPkcs1Sig.Hash) (em em' : List Byte) (v : State) : Prop where
  mid : Mid s v
  x14 : v.gpr .x14 = fb s + BitVec.ofNat 64 oEM1
  x15 : v.gpr .x15 = fb s + BitVec.ofNat 64 oEM2
  x13 : v.gpr .x13 = BitVec.ofNat 64 (s.gpr .x3).toNat
  b1 : Spec.Rsa.bytesAt v.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em
  b2 : Spec.Rsa.bytesAt v.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .x3).toNat = em'
  val : Spec.Rsa.bytesAt v.mem (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - h.len)

/-- After `compare`: its result, and the hash value in `EM₁`. -/
structure AfterCmp (s : State) (h : Spec.RsaPkcs1Sig.Hash) (em em' : List Byte) (y : State) : Prop where
  mid : Mid s y
  hiff : y.gpr .x12 = 0 ↔ em = em'
  val : Spec.Rsa.bytesAt y.mem (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - h.len)

/-! ## The restores, and the whole function -/

/-- The restores, then the frame's release: the caller's registers are back,
and `x0` and memory are kept. -/
theorem restore_ok {s w : State} (hm : Mid s w) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ (freed frameBytes w').gpr .x0 = w.gpr .x0 ∧
        (freed frameBytes w').mem = w.mem := by
  unfold restore
  refine wp_addSp (by decide) fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .x16) (l := saved) (B := fb s) e₁ saved_ho (by decide)
    (fun p hp' => by
      rw [o₁.rd, o₁.wr, hm.wr]
      exact InRegions_append_cons (xs := w.rd) |>.mpr (.inl (Offset.contains_base _
        (by have := saved_offs p hp'; unfold frameBytes; omega_arith) (by have := saved_offs p hp'; omega_arith))))
    (by rw [o₁.mem]; exact hm.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, fun r hr' => ?_⟩, ?_, ?_⟩
  · simp only [freed]
    by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      exact hr.gpr p hp'
    · have hr'' : r ∈ [Reg.x23, .x24, .x25, .x26, .x27, .x28] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> first | decide | simp_all [saved]
      have h16 : r ∉ [Reg.x16] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'' ⊢
        rcases hr'' with h | h | h | h | h | h <;> subst h <;> decide
      rw [hr.other r hs, o₁.gpr r h16]
      exact hm.hi r hr''
  · simp only [freed]
    rw [hr.sp, o₁.sp, hm.sp, BitVec.sub_add_cancel]
  · simp only [freed]
    rw [hr.v, o₁.vcs r hr', hm.v r hr']
  · simp only [freed]
    rw [hr.other .x0 (by decide), o₁.get .x0]
  · simp only [freed]
    rw [hr.mem, o₁.mem]

theorem recover_eq {s : State} (h : Spec.RsaPkcs1Sig.Hash) (hsig : stackArg s 0 = s.gpr .x3) :
    Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) h
      (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat) = recOut s h := by
  rw [recover_eq_recoverEnc, recoverEnc, bytesAt_length, bytesAt_length, hsig, ite_eq_left rfl]
  rfl

theorem recover_none {s : State} (h : Spec.RsaPkcs1Sig.Hash) (hsig : stackArg s 0 ≠ s.gpr .x3) :
    Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) h
      (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat) = none := by
  rw [recover_eq_recoverEnc, recoverEnc, bytesAt_length, bytesAt_length,
    ite_eq_right fun e => hsig (BitVec.eq_of_toNat_eq e)]

theorem lenCheck_ok {K : Nat} {s : State} (hp : PreR K s) :
    WP isa (.block lenCheck) s fun t₁ => Only [.x8] s t₁ ∧ t₁.gpr .x8 = stackArg s 0 - s.gpr .x3 := by
  refine VG.Proof.RsaPkcs1Sig.AArch64.wp_ldrSp (by decide) ?_ fun t₀ o₀ e₀ =>
    wp_sub fun t₁ o₁ e₁ => wp_nil ⟨(o₀.trans o₁).mono, ?_⟩
  · have h := arg_in (s := s) (j := 0) (rs := s.rd ++ s.wr) hp (Covers.left (Covers.refl _)) (by decide)
    simpa [stackArgAddr] using h
  · rw [e₁, e₀, o₀.get .x3, BitVec.add_zero, ← VG.Proof.RsaPkcs1Sig.AArch64.sa0 s]; rfl

theorem eval_len {s t : State} (e : t.gpr .x8 = stackArg s 0 - s.gpr .x3) :
    isa.eval (.nonzero .x .x8) t = some (decide (stackArg s 0 ≠ s.gpr .x3)) := by
  rw [eval_nonzero, e, ne_zero_iff, BitVec.toNat_sub]
  have := (stackArg s 0).isLt; have := (s.gpr .x3).isLt
  refine congrArg some (decide_eq_decide.mpr ⟨fun h e => ?_, fun h e => h ?_⟩)
  · rw [e] at h; omega_arith
  · apply BitVec.eq_of_toNat_eq; omega_arith

/-- Zeros to `out`, from the entry state but for `x8`. -/
theorem zeroArgs_ok {K : Nat} {s t : State} (hp : PreR K s) (o : Only [.x8] s t) :
    WP isa zeroArgs t fun w => Keep [.x8, .x14, .x13, .x15, .x13, .x14, .x0] s w ∧
      Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat ((w.gpr .x0).setWidth 32) none := by
  obtain ⟨hl0, hl1⟩ := hlen hp
  have := hp.k2
  unfold zeroArgs
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_nil ?_)
  have O₂ : Only [.x8, .x14, .x13] s u₂ := (o.trans (o₁.trans o₂)).mono
  refine WP.mono (zeroOut_ok (p := s.gpr .x0) (n := (s.gpr .x1).toNat) hl0 (by omega_arith)
    (by rw [o₂.get .x14, e₁, o.get .x0]) (by rw [e₂, o₁.get .x1, o.get .x1, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [O₂.wr]; exact out_wr hp [])) fun w ⟨k, mw, x0⟩ => ⟨(O₂.keep.trans k).mono, by rw [x0]; rfl, ?_⟩
  rw [mw, O₂.mem]
  have := bytesAt_writeBytes s.mem (s.gpr .x0) (List.replicate (s.gpr .x1).toNat 0) (by simp; omega_arith)
  rwa [List.length_replicate] at this

end VG.Proof.RsaPkcs1Sig.AArch64.Rec
