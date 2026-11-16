module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCall
import VerifiedGarbage.Proof.MlKem.AArch64.Wp

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
