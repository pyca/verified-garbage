import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame

/-!
# `vg_rsa_pkcs1_sign` on AArch64: the block before `encode`

`encArgs_ok`: the registers saved, `k` kept in `x19` and `out` in `x17`,
and `encode`'s arguments set up (`AtEnc`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov wp_movw)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (Saved.congr)

/-- Before `encode`: the registers saved in their slots, `k` in `x19`, `out`
in `x17`, `sp` in `x16`, and `encode`'s arguments: `EM`, `k`, `hash`, the
hash value and its length. -/
structure AtEnc (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr
  g : ∀ r, r ∉ [Reg.x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19] → u.gpr r = s.gpr r
  x8 : u.gpr .x8 = fb s + BitVec.ofNat 64 oEM
  x9 : u.gpr .x9 = s.gpr .x3
  x10 : u.gpr .x10 = ((s.gpr .x6).setWidth 32).setWidth 64
  x11 : u.gpr .x11 = s.gpr .x7
  x12 : u.gpr .x12 = stackArg s 0
  x16 : u.gpr .x16 = fb s
  x17 : u.gpr .x17 = s.gpr .x0
  x19 : u.gpr .x19 = s.gpr .x3
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem u.mem
  sv : Spill.Saved (fb s) s.gpr saved u.mem

theorem wr_frame {s t : State} (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) {d n : Nat}
    (h : d + n ≤ frameBytes) : InRegions t.wr (fb s + BitVec.ofNat 64 d) n := by
  rw [hwr]; exact in_frame s _ h

theorem encArgs_ok {K : Nat} {s u : State} (hp : PreS K s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block encArgs) u (AtEnc s) := by
  unfold encArgs save
  simp only [List.cons_append]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  have hin : ∀ p ∈ saved, InRegions u₁.wr (u₁.gpr .x16 + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [e₁, o₁.wr]; exact wr_frame hwr (by have := saved_offs p hp'; unfold frameBytes; omega)
  refine Spill.save_ok (b := .x16) (l := saved) saved_ho hin ?_
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : State, u₂ = { u₁ with mem := Spill.saveMem u₁.mem (u₁.gpr .x16) u₁.gpr saved } :=
    ⟨_, rfl⟩
  rw [← hu₂]
  have m₂ : Frame [⟨fb s, frameBytes⟩] s.mem u₂.mem := by
    rw [hu₂, e₁, o₁.mem, hm]
    exact Spill.saveMem_frame_base (fun p hp' => by have := saved_offs p hp'; unfold frameBytes; omega)
      (by decide) _ _ _
  have sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [hu₂, e₁]
    refine Saved.congr (Spill.saveMem_saved (by decide) _ _ _) fun p hp' => ?_
    have : p.1 ≠ .x16 := by revert p; decide
    rw [o₁.get p.1 (by simpa using this), hg]
  have g₂ : ∀ r, u₂.gpr r = u₁.gpr r := fun r => by rw [hu₂]
  refine wp_mov fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_addSp (by decide) fun u₅ o₅ e₅ =>
    wp_mov fun u₆ o₆ e₆ => wp_movw fun u₇ o₇ e₇ => wp_mov fun u₈ o₈ e₈ => ?_
  have O₈ : Only [.x19, .x17, .x8, .x9, .x10, .x11] u₂ u₈ :=
    (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))).mono
  have sp₈ : u₈.sp = fb s := by rw [O₈.sp, hu₂]; show u₁.sp = _; rw [o₁.sp, hsp]
  have rd₈ : u₈.rd = s.rd := by rw [O₈.rd, hu₂]; show u₁.rd = _; rw [o₁.rd, hrd]
  have wr₈ : u₈.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₈.wr, hu₂]; show u₁.wr = _; rw [o₁.wr, hwr]
  have a₀ : u₈.sp + BitVec.ofNat 64 frameBytes = stackArgAddr s 0 := by
    rw [sp₈, stackArgAddr_fb, Nat.mul_zero, Nat.add_zero]
  refine wp_ldrSp (by decide) (by rw [a₀, rd₈]; exact arg_in hp (Covers.left (Covers.refl _)) (by decide))
    fun u₉ o₉ e₉ => wp_nil ?_
  rw [a₀, O₈.mem, arg_frame hp m₂ (by decide)] at e₉
  have gs : ∀ r, r ≠ .x16 → u₁.gpr r = s.gpr r := fun r h => by rw [o₁.gpr r (by simpa using h), hg]
  refine ⟨?sp, ?rd, ?wr, ?g, ?x8, ?x9, ?x10, ?x11, ?x12, ?x16, ?x17, ?x19, ?v, ?mem, ?sv⟩
  case sp => rw [o₉.sp, sp₈]
  case rd => rw [o₉.rd, rd₈]
  case wr => rw [o₉.wr, wr₈]
  case g =>
    intro r hr
    have sub₁ : ∀ r : Reg, r ∈ [Reg.x19, .x17, .x8, .x9, .x10, .x11] →
        r ∈ [Reg.x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19] := by decide
    have sub₂ : ∀ r : Reg, r ∈ [Reg.x12] → r ∈ [Reg.x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19] := by decide
    have h₃ : r ≠ .x16 := fun h => hr (by subst h; decide)
    rw [o₉.gpr r fun h => hr (sub₂ r h), O₈.gpr r fun h => hr (sub₁ r h), g₂, gs r h₃]
  case x8 =>
    have : u₂.sp = fb s := by rw [hu₂]; show u₁.sp = _; rw [o₁.sp, hsp]
    rw [o₉.get .x8, o₈.get .x8, o₇.get .x8, o₆.get .x8, e₅, o₄.sp, o₃.sp, this]
  case x9 => rw [o₉.get .x9, o₈.get .x9, o₇.get .x9, e₆, o₅.get .x3, o₄.get .x3, o₃.get .x3, g₂, gs .x3 (by decide)]
  case x10 => rw [o₉.get .x10, o₈.get .x10, e₇, o₆.get .x6, o₅.get .x6, o₄.get .x6, o₃.get .x6, g₂,
    gs .x6 (by decide)]
  case x11 => rw [o₉.get .x11, e₈, o₇.get .x7, o₆.get .x7, o₅.get .x7, o₄.get .x7, o₃.get .x7, g₂,
    gs .x7 (by decide)]
  case x12 => rw [e₉]
  case x16 => rw [o₉.get .x16, O₈.get .x16, g₂, e₁]
  case x17 => rw [o₉.get .x17, o₈.get .x17, o₇.get .x17, o₆.get .x17, o₅.get .x17, e₄, o₃.get .x0, g₂,
    gs .x0 (by decide)]
  case x19 => rw [o₉.get .x19, o₈.get .x19, o₇.get .x19, o₆.get .x19, o₅.get .x19, o₄.get .x19, e₃, g₂,
    gs .x3 (by decide)]
  case v =>
    intro r hr
    rw [o₉.vcs r hr, O₈.vcs r hr, hu₂]
    show (u₁.v r).extractLsb' 0 64 = _
    rw [o₁.vcs r hr, hv r hr]
  case mem => rw [o₉.mem, O₈.mem]; exact m₂
  case sv => rw [o₉.mem, O₈.mem]; exact sv₂

end VG.Proof.RsaPkcs1Sig.AArch64.Sgn
