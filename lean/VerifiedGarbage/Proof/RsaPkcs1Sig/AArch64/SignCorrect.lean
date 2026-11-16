module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify

/-! ### `RsaPkcs1Sig.AArch64.SignCall`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.AArch64.SignFrame`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_sign` on AArch64: the block before `encode`

`encArgs_ok`: the registers saved, `k` kept in `x19` and `out` in `x17`,
and `encode`'s arguments set up (`AtEnc`).
-/

@[expose] public section

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
    have : p.1 ≠ .x16 := by revert p; decide
    rw [o₁.get p.1 (by simpa using this), hg]
  obtain g₂ : ∀ r, u₂.gpr r = u₁.gpr r := fun r => by rw [hu₂]
  refine wp_mov fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_addSp (by decide) fun u₅ o₅ e₅ =>
    wp_mov fun u₆ o₆ e₆ => wp_movw fun u₇ o₇ e₇ => wp_mov fun u₈ o₈ e₈ => ?_
  obtain O₈ : Only [.x19, .x17, .x8, .x9, .x10, .x11] u₂ u₈ :=
    (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))).mono
  obtain sp₈ : u₈.sp = fb s := by rw [O₈.sp, hu₂]; show u₁.sp = _; rw [o₁.sp, hsp]
  obtain rd₈ : u₈.rd = s.rd := by rw [O₈.rd, hu₂]; show u₁.rd = _; rw [o₁.rd, hrd]
  obtain wr₈ : u₈.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₈.wr, hu₂]; show u₁.wr = _; rw [o₁.wr, hwr]
  obtain a₀ : u₈.sp + BitVec.ofNat 64 frameBytes = stackArgAddr s 0 := by
    rw [sp₈, stackArgAddr_fb, Nat.mul_zero, Nat.add_zero]
  refine wp_ldrSp (by decide) (by rw [a₀, rd₈]; exact arg_in hp (Covers.left (Covers.refl _)) (by decide))
    fun u₉ o₉ e₉ => wp_nil ?_
  rw [a₀, O₈.mem, arg_frame hp m₂ (by decide)] at e₉
  obtain gs : ∀ r, r ≠ .x16 → u₁.gpr r = s.gpr r := fun r h => by rw [o₁.gpr r (by simpa using h), hg]
  refine ⟨?sp, ?rd, ?wr, ?g, ?x8, ?x9, ?x10, ?x11, ?x12, ?x16, ?x17, ?x19, ?v, ?mem, ?sv⟩
  case sp => rw [o₉.sp, sp₈]
  case rd => rw [o₉.rd, rd₈]
  case wr => rw [o₉.wr, wr₈]
  case g =>
    intro r hr
    obtain sub₁ : ∀ r : Reg, r ∈ [Reg.x19, .x17, .x8, .x9, .x10, .x11] →
        r ∈ [Reg.x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19] := by decide
    obtain sub₂ : ∀ r : Reg, r ∈ [Reg.x12] → r ∈ [Reg.x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19] := by decide
    obtain h₃ : r ≠ .x16 := fun h => hr (by subst h; decide)
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

end

end


/-!
# `vg_rsa_pkcs1_sign` on AArch64: the call of `vg_rsa_private_checked`

`callArgs_ok`: after the encoding into `EM`, the function's stack arguments
`p` … `scratch_len` are copied to the call's (`copies_ok`), and the
registers set up (`AtCall`); `call_ok`: the call writes the signature of
`EM` to `out` and keeps `k` in `x19` and the saved slots (`AfterCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Sign VG.WriteBytes
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov wp_movw clob)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes bytes_apart)

/-! ## The stack arguments -/

/-- After copying `n` stack arguments from `v₀`. -/
structure Copied (s v₀ : State) (n : Nat) (v : State) : Prop where
  sp : v.sp = v₀.sp
  rd : v.rd = v₀.rd
  wr : v.wr = v₀.wr
  g : ∀ r, r ≠ .x15 → v.gpr r = v₀.gpr r
  vc : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (v₀.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, 112⟩] v₀.mem v.mem
  args : ∀ i < n, v.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (i + 1)

/-- Our first `N` stack arguments can be read, and are apart from the
stack the function uses. -/
structure ArgsOk (K : Nat) (s : State) (N : Nat) : Prop where
  rd : ∀ j < N, InRegions s.rd (stackArgAddr s j) 8
  kd : ∀ j < N, (kR K s).Disjoint ⟨stackArgAddr s j, 8⟩

theorem PreS.argsOk {K : Nat} {s : State} (hp : PreS K s) : ArgsOk K s 13 :=
  ⟨fun _ hj => arg_in hp (Covers.refl _) hj, fun j hj => hp.ka.sub_right (by
    rw [stackArgAddr_eq s j]; exact Offset.sub_base _ (by omega_arith))⟩

theorem ArgsOk.frame {K : Nat} {s : State} {N : Nat} (hA : ArgsOk K s N) {m : Mem}
    (h : Frame [⟨fb s, frameBytes⟩] s.mem m) {j : Nat} (hj : j < N) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := ⟨stackArgAddr s j, 8⟩) (Region.contains_self _ _) (keep_of_frame (hA.kd j hj)) (by decide)

theorem copies_ok {K N : Nat} {s v₀ : State} (hA : ArgsOk K s N) (hsp : v₀.sp = fb s)
    (h16 : v₀.gpr .x16 = fb s) (hrd : v₀.rd = s.rd) (hwr : v₀.wr = ⟨fb s, frameBytes⟩ :: s.wr)
    (hm : Frame [⟨fb s, frameBytes⟩] s.mem v₀.mem) :
    ∀ n, n + 1 ≤ N → n ≤ 14 → WP isa (.block ((List.range n).flatMap copyArg)) v₀ (Copied s v₀ n) := by
  intro n
  induction n with
  | zero => exact fun _ _ => wp_nil ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, Frame.refl _ _, fun i hi => absurd hi (by omega_arith)⟩
  | succ n ih =>
    intro hN hn
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith) (by omega_arith)) fun v hv => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, copyArg, List.append_nil]
    obtain a₁ : v.sp + BitVec.ofNat 64 (frameBytes + 8 * (n + 1)) = stackArgAddr s (n + 1) := by
      rw [hv.sp, hsp, stackArgAddr_fb]
    obtain hmv : Frame [⟨fb s, frameBytes⟩] s.mem v.mem := hm.trans (hv.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨fb s, frameBytes⟩, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
    refine wp_ldrSp (by unfold frameBytes; omega_arith) (by
      rw [a₁, hv.rd, hrd]; exact Covers.left (Covers.refl _) _ _ (hA.rd _ (by omega_arith))) fun v₁ o₁ e₁ => ?_
    rw [a₁, hA.frame hmv (by omega_arith)] at e₁
    obtain x16 : v₁.gpr .x16 = fb s := by rw [o₁.get .x16, hv.g .x16 (by decide), h16]
    refine wp_strx (a := fb s + BitVec.ofNat 64 (8 * n)) (by omega_arith) (by rw [x16])
      (by rw [o₁.wr, hv.wr, hwr]; exact in_frame _ _ (by unfold frameBytes; omega_arith)) fun v₂ m₂ => wp_nil ?_
    obtain mem₂ : v₂.mem = v.mem.writeW (fb s + BitVec.ofNat 64 (8 * n)) (stackArg s (n + 1)) := by
      rw [m₂.mem, o₁.mem, e₁]
    refine ⟨by rw [m₂.sp, o₁.sp, hv.sp], by rw [m₂.rd, o₁.rd, hv.rd], by rw [m₂.wr, o₁.wr, hv.wr],
      fun r hr => by rw [m₂.gpr, o₁.gpr r (by simpa using hr), hv.g r hr],
      fun r hr => by rw [m₂.vcs r hr, o₁.vcs r hr, hv.vc r hr], ?_, fun i hi => ?_⟩
    · rw [mem₂]
      exact hv.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    · rw [mem₂]
      rcases (by omega_arith : i < n ∨ i = n) with h | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), hv.args i h]
      · exact Mem.readW_writeW_self64 _ _ _


/-! ## The call's arguments -/

/-- `EM`, of `k` bytes. -/
abbrev emR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .x3).toNat⟩

theorem em_sub {K : Nat} {s : State} (hp : PreS K s) : Region.Sub (emR s) (kR K s) :=
  frame_sub K s (by have := hp.k2; unfold oEM frameBytes; omega_arith)

theorem a96_sub (K : Nat) (s : State) : Region.Sub ⟨fb s, 96⟩ (kR K s) :=
  fun a h => frame_sub0 K s a (Region.sub_prefix (by decide) a h)

/-- The slots of the saved registers are apart from `EM`. -/
theorem slots_em {K : Nat} {s : State} (hp : PreS K s) {n : Nat} (hn : n ≤ (s.gpr .x3).toNat) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 112, 16⟩ ⟨fb s + BitVec.ofNat 64 oEM, n⟩ :=
  Offset.disjoint _ (by unfold oEM; omega_arith) (by decide) (by have := hp.k2; unfold oEM; omega_arith)

/-- At the call: `k` in `x19`, the arguments of `vg_rsa_private_checked`
set up, and `EM` holding `em`. -/
structure AtCall (s : State) (em : List Byte) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x0 : t.gpr .x0 = s.gpr .x0
  x1 : t.gpr .x1 = s.gpr .x1
  x2 : t.gpr .x2 = s.gpr .x2
  x3 : t.gpr .x3 = s.gpr .x3
  x4 : t.gpr .x4 = s.gpr .x4
  x5 : t.gpr .x5 = s.gpr .x5
  x6 : t.gpr .x6 = fb s + BitVec.ofNat 64 oEM
  x7 : t.gpr .x7 = s.gpr .x3
  x19 : t.gpr .x19 = s.gpr .x3
  hi : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  args : ∀ i < 12, stackArg t i = stackArg s (i + 1)
  mem : Frame [⟨fb s, frameBytes⟩] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  em : Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .x3).toNat = em

theorem callArgsN_ok {K : Nat} {s u w : State} (hp : PreS K s) {n : Nat} (hA : ArgsOk K s (n + 1))
    (hn₁ : 12 ≤ n) (hn₂ : n ≤ 14) (hu : AtEnc s u) (hK : Keep clob u w)
    {em : List Byte} (hme : w.mem = writeBytes u.mem (u.gpr .x8) em) (hl : em.length = (s.gpr .x3).toNat) :
    WP isa (.block (callArgsN n)) w fun t => AtCall s em t ∧ ∀ i < n, stackArg t i = stackArg s (i + 1) := by
  have hk2 := hp.k2
  obtain g : ∀ r, r ∉ clob → r ∉ [Reg.x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19] → w.gpr r = s.gpr r :=
    fun r h₁ h₂ => by rw [hK.gpr r h₁, hu.g r h₂]
  obtain fw : Frame [⟨fb s + BitVec.ofNat 64 oEM, em.length⟩] u.mem w.mem := by
    rw [hme, hu.x8]; exact frame_writeBytes _ _ _
  obtain hmw : Frame [⟨fb s, frameBytes⟩] s.mem w.mem := hu.mem.trans (fw.sub fun r hr => by
    rw [List.mem_singleton.mp hr, hl]
    exact ⟨⟨fb s, frameBytes⟩, List.mem_singleton_self _, Offset.sub_base _ (by unfold oEM frameBytes; omega_arith)⟩)
  obtain svw : Spill.Saved (fb s) s.gpr saved w.mem := hu.sv.frame_in saved_offs fw fun r hr => by
    rw [List.mem_singleton.mp hr, hl]; exact slots_em hp (Nat.le_refl _)
  obtain emw : Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .x3).toNat = em := by
    rw [hme, hu.x8, ← hl, bytesAt_writeBytes _ _ _ (by omega_arith)]
  unfold callArgsN
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok hA (v₀ := w) (by rw [hK.sp, hu.sp]) (by rw [hK.get .x16, hu.x16])
    (by rw [hK.rd, hu.rd]) (by rw [hK.wr, hu.wr]) hmw n (Nat.le_refl _) hn₂) fun v hv => ?_
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_nil ?_
  obtain O₃ : Only [.x0, .x6, .x7] v v₃ := (o₁.trans (o₂.trans o₃)).mono
  obtain hv15 : ∀ r, r ∉ clob → r ∉ [Reg.x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19] → r ≠ .x15 →
      r ∉ [Reg.x0, .x6, .x7] → v₃.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [O₃.gpr r h₄, hv.g r h₃, g r h₁ h₂]
  obtain d96 : ∀ {R : Region}, R.Disjoint ⟨fb s, 112⟩ → R.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt v₃.mem R.base R.len = Spec.Rsa.bytesAt w.mem R.base R.len := fun hd hl' => by
    rw [O₃.mem]; exact bytes_apart hv.mem hd hl'
  obtain hargs : ∀ i < n, stackArg v₃ i = stackArg s (i + 1) := fun i hi => by
    show v₃.mem.readW (v₃.sp + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [O₃.mem, O₃.sp, hv.sp, hK.sp, hu.sp, hv.args i hi]
  refine ⟨⟨?sp, ?rd, ?wr, ?x0, ?x1, ?x2, ?x3, ?x4, ?x5, ?x6, ?x7, ?x19, ?hi, ?v, ?args, ?mem, ?sv, ?em⟩, ?ex⟩
  case sp => rw [O₃.sp, hv.sp, hK.sp, hu.sp]
  case rd => rw [O₃.rd, hv.rd, hK.rd, hu.rd]
  case wr => rw [O₃.wr, hv.wr, hK.wr, hu.wr]
  case x0 => rw [o₃.get .x0, o₂.get .x0, e₁, hv.g .x17 (by decide), hK.get .x17, hu.x17]
  case x1 => exact hv15 .x1 (by decide) (by decide) (by decide) (by decide)
  case x2 => exact hv15 .x2 (by decide) (by decide) (by decide) (by decide)
  case x3 => exact hv15 .x3 (by decide) (by decide) (by decide) (by decide)
  case x4 => exact hv15 .x4 (by decide) (by decide) (by decide) (by decide)
  case x5 => exact hv15 .x5 (by decide) (by decide) (by decide) (by decide)
  case x6 => rw [o₃.get .x6, e₂, o₁.get .x8, hv.g .x8 (by decide), hK.get .x8, hu.x8]
  case x7 => rw [e₃, o₂.get .x19, o₁.get .x19, hv.g .x19 (by decide), hK.get .x19, hu.x19]
  case x19 => rw [O₃.get .x19, hv.g .x19 (by decide), hK.get .x19, hu.x19]
  case hi =>
    intro r hr
    exact hv15 r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
  case v =>
    intro r hr
    rw [O₃.vcs r hr, hv.vc r hr, hK.vcs r hr, hu.v r hr]
  case args => exact fun i hi => hargs i (by omega_arith)
  case mem =>
    rw [O₃.mem]
    exact hmw.trans (hv.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨fb s, frameBytes⟩, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
  case sv =>
    rw [O₃.mem]
    exact svw.frame_in saved_offs hv.mem fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)
  case em =>
    rw [← emw]
    exact d96 (R := ⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .x3).toNat⟩)
      (Offset.disjoint_base _ (by unfold oEM; omega_arith) (by unfold oEM; omega_arith)) (by dsimp only; omega_arith)
  case ex => exact hargs

theorem callArgs_ok {K : Nat} {s u w : State} (hp : PreS K s) (hu : AtEnc s u) (hK : Keep clob u w)
    {em : List Byte} (hme : w.mem = writeBytes u.mem (u.gpr .x8) em) (hl : em.length = (s.gpr .x3).toNat) :
    WP isa (.block callArgs) w (AtCall s em) :=
  WP.mono (callArgsN_ok hp hp.argsOk (by decide) (by decide) hu hK hme hl) fun _ h => h.1


/-! ## The call -/

theorem privOk_ofK {K : Nat} (hpos : 0 < K) (hcl : K ≤ 2 ^ 20) {s t : State} (hp : PreS K s) {em : List Byte}
    (ha : AtCall s em t) : PrivOk K t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hfK : fb s - BitVec.ofNat 64 K = kb K s := by rw [fb_eq K, BitVec.add_sub_cancel]
  have hkK : Region.Sub ⟨kb K s, K⟩ (kR K s) := Region.sub_prefix (by unfold stk; omega_arith)
  have a1 := ha.args 0 (by decide); have a2 := ha.args 1 (by decide); have a3 := ha.args 2 (by decide)
  have a4 := ha.args 3 (by decide); have a5 := ha.args 4 (by decide); have a6 := ha.args 5 (by decide)
  have a7 := ha.args 6 (by decide); have a8 := ha.args 7 (by decide); have a9 := ha.args 8 (by decide)
  have a10 := ha.args 9 (by decide); have a11 := ha.args 10 (by decide); have a12 := ha.args 11 (by decide)
  have hem : (⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .x3).toNat⟩ : Region) =
      ⟨kb K s + BitVec.ofNat 64 (K + oEM), (s.gpr .x3).toNat⟩ := by rw [off_fb K]
  have ha96 : (⟨fb s, 96⟩ : Region) = ⟨kb K s + BitVec.ofNat 64 K, 96⟩ := by rw [fb_eq K]
  have hfbE : (fb s + BitVec.ofNat 64 oEM).toNat = (fb s).toNat + oEM := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM frameBytes at *; omega_arith
  refine ⟨?hl, ?hrd, ?hwr, ?hk, ?h1, ?h7, ?he1, ?he2, ?hp1, ?hp2, ?hq1, ?hq2, ?hdp, ?hqi, ?hdq, ?hs⟩
  case hl =>
    simp only [Nat.zero_add, Nat.reduceAdd] at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    rw [ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, a12]
    exact {
      sp1 := by unfold stk at *; omega_arith
      sp2 := by omega_arith
      on := hp.on
      oe := hp.oe
      oi := (hp.ko.sub_left (em_sub hp)).symm
      op := hp.op
      oq := hp.oq
      odp := hp.odp
      odq := hp.odq
      oqi := hp.oqi
      os := hp.os
      oa := (hp.ko.sub_left (a96_sub K s)).symm
      ns := hp.ns
      es := hp.es
      is := hp.ks.sub_left (em_sub hp)
      ps := hp.ps
      qs := hp.qs
      dps := hp.dps
      dqs := hp.dqs
      qis := hp.qis
      sa := (hp.ks.sub_left (a96_sub K s)).symm
      ko := by rw [hfK]; exact hp.ko.sub_left hkK
      kn := by rw [hfK]; exact hp.kn.sub_left hkK
      ke := by rw [hfK]; exact hp.ke.sub_left hkK
      ki := by
        rw [hfK, hem]
        exact Offset.base_disjoint _ (by unfold oEM; omega_arith) (by unfold oEM stk frameBytes at *; omega_arith)
      kp := by rw [hfK]; exact hp.kp.sub_left hkK
      kq := by rw [hfK]; exact hp.kq.sub_left hkK
      kdp := by rw [hfK]; exact hp.kdp.sub_left hkK
      kdq := by rw [hfK]; exact hp.kdq.sub_left hkK
      kqi := by rw [hfK]; exact hp.kqi.sub_left hkK
      ks := by rw [hfK]; exact hp.ks.sub_left hkK
      ka := by rw [hfK, ha96]; exact Offset.base_disjoint _ (by omega_arith) (by unfold stk at *; omega_arith)
      wo := hp.wo
      wn := hp.wn
      we := hp.we
      wi := by dsimp only; rw [hfbE]; unfold oEM frameBytes at *; omega_arith
      wp := hp.wp
      wq := hp.wq
      wdp := hp.wdp
      wdq := hp.wdq
      wqi := hp.wqi
      ws := hp.ws }
  case hrd =>
    simp only [privRd]
    simp only [Nat.zero_add, Nat.reduceAdd] at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    rw [ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ha.rd, ha.wr]
    have hm : ∀ r ∈ [nR s, eR s, dR s, pR s, qR s, dpR s, dqR s, qiR s, aR s],
        Covers [r] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)) :=
      fun r hr => Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
        hp.hrd)
    refine Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp)) (Covers.cons
      (Covers.right (Covers.one (in_frame _ _ (by unfold oEM frameBytes; omega_arith))))
      (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp))
      (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp))
      (Covers.right (Covers.one ?_)))))))))
    simpa using in_frame s s.wr (d := 0) (n := 96) (by decide)
  case hwr =>
    simp only [privWr]
    have a11' := a11; have a12' := a12
    simp only [Nat.reduceAdd] at a11' a12'
    rw [ha.x0, ha.x1, a11', a12', ha.wr]
    exact Covers.cons (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ hp.hwo)
      (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ hp.hws)
  case hk => rw [ha.x3]; exact ⟨hk1, hk2⟩
  case h1 => rw [ha.x1, ha.x3, hp.ol]
  case h7 => rw [ha.x7, ha.x3]
  case he1 => rw [ha.x5]; exact hp.e1
  case he2 => rw [ha.x5, ha.x3]; exact hp.e2
  case hp1 => rw [a2]; exact hp.p1
  case hp2 => rw [a2, ha.x3]; exact hp.p2
  case hq1 => rw [a4]; exact hp.q1
  case hq2 => rw [a4, ha.x3]; exact hp.q2
  case hdp => rw [a6, a2]; exact hp.hdp
  case hqi => rw [a10, a2]; exact hp.hqi
  case hdq => rw [a8, a4]; exact hp.hdq
  case hs => rw [a12, ha.x3]; unfold Spec.Rsa.scratchWords; exact hp.hs


theorem privOk_of (c : PrivChecked) {s t : State} (hp : PreS c.stack s) {em : List Byte} (ha : AtCall s em t) :
    PrivOk c.stack t :=
  privOk_ofK c.pos c.le hp ha

/-- The private operation on `em`, with the key as the entry state gives it. -/
def privOut (s : State) (em : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) em
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)

/-- In the frame after the call: the registers saved, `k` in `x19`. -/
structure Mid (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : t.gpr .x19 = s.gpr .x3
  hi : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  sv : Spill.Saved (fb s) s.gpr saved t.mem

/-- After the call: `Mid`, and `out` written with the result. -/
structure AfterCall (s : State) (em : List Byte) (t : State) : Prop extends Mid s t where
  res : Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (privOut s em)

/-- A buffer of the caller, in memory changed only in the frame. -/
theorem bytes_frame {K : Nat} {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {p : Addr}
    {len : Nat} (hk : (kR K s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len :=
  bytes_apart (R := ⟨p, len⟩) hf (hk.sub_left (frame_sub0 K s)).symm hl

/-- The call's results, from what its contract gives. -/
theorem afterCall_of {K D : Nat} (hcl : K ≤ 2 ^ 20) (hd : 16 * D ≤ K) {s t s' : State} (hp : PreS K s)
    {em : List Byte} (ha : AtCall s em t) (hrd' : s'.rd = t.rd) (hwr' : s'.wr = t.wr) (hsp' : s'.sp = t.sp)
    (hf : Frame (privWr t ++ [below t.sp (16 * D)]) t.mem s'.mem)
    (hpres : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = t.gpr r)
    (hvs : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hpost : Spec.Rsa.writtenOutcome s'.mem (t.gpr .x0) (t.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
        (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt t.mem (t.gpr .x2) (t.gpr .x3).toNat)
          (Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat)
          (Spec.Rsa.bytesAt t.mem (t.gpr .x6) (t.gpr .x3).toNat)
          (Spec.Rsa.bytesAt t.mem (stackArg t 0) (stackArg t 1).toNat)
          (Spec.Rsa.bytesAt t.mem (stackArg t 2) (stackArg t 3).toNat)
          (Spec.Rsa.bytesAt t.mem (stackArg t 4) (stackArg t 1).toNat)
          (Spec.Rsa.bytesAt t.mem (stackArg t 6) (stackArg t 3).toNat)
          (Spec.Rsa.bytesAt t.mem (stackArg t 8) (stackArg t 1).toNat))) :
    AfterCall s em s' := by
  obtain hfb := fb_toNat hp
  obtain hkb := kb_toNat hp
  obtain a1 := ha.args 0 (by decide); have a2 := ha.args 1 (by decide); have a3 := ha.args 2 (by decide)
  obtain a4 := ha.args 3 (by decide); have a5 := ha.args 4 (by decide); have a6 := ha.args 5 (by decide)
  obtain a7 := ha.args 6 (by decide); have a8 := ha.args 7 (by decide); have a9 := ha.args 8 (by decide)
  obtain a10 := ha.args 9 (by decide); have a11 := ha.args 10 (by decide); have a12 := ha.args 11 (by decide)
  simp only [Nat.zero_add, Nat.reduceAdd] at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  simp only [privWr] at hf
  rw [ha.x0, ha.x1, a11, a12, ha.sp] at hf
  obtain hl : ∀ {p : Addr} {len : Nat}, p.toNat + len ≤ 2 ^ 64 → len ≤ 2 ^ 64 := fun h => by omega_arith
  rw [ha.x0, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, a1, a2, a3, a4, a5, a7, a9, ha.em,
    bytes_frame ha.mem hp.kn (hl hp.wn), bytes_frame ha.mem hp.ke (hl hp.we),
    bytes_frame ha.mem hp.kp (hl hp.wp), bytes_frame ha.mem hp.kq (hl hp.wq),
    bytes_frame ha.mem (len := (stackArg s 2).toNat) (by rw [← hp.hdp]; exact hp.kdp)
      (by have := hp.wdp; rw [hp.hdp] at this; omega_arith),
    bytes_frame ha.mem (len := (stackArg s 4).toNat) (by rw [← hp.hdq]; exact hp.kdq)
      (by have := hp.wdq; rw [hp.hdq] at this; omega_arith),
    bytes_frame ha.mem (len := (stackArg s 2).toNat) (by rw [← hp.hqi]; exact hp.kqi)
      (by have := hp.wqi; rw [hp.hqi] at this; omega_arith)] at hpost
  exact {
    sp := hsp'.trans ha.sp
    rd := hrd'.trans ha.rd
    wr := hwr'.trans ha.wr
    x19 := (hpres .x19 (by decide) (by decide)).trans ha.x19
    hi := fun r hr => (hpres r (by revert r; decide) (by revert r; decide)).trans (ha.hi r hr)
    v := fun r hr => (hvs r hr).trans (ha.v r hr)
    sv := ha.sv.frame_in saved_offs hf fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ko.sub_left (frame_sub K s (d := 112) (n := 16) (by decide))
      · exact hp.ks.sub_left (frame_sub K s (d := 112) (n := 16) (by decide))
      · exact Offset.disjoint_below (fb s) (by omega_arith)
    res := hpost }

theorem call_ok (c : PrivChecked) {s t : State} (hp : PreS c.stack s) {em : List Byte} (ha : AtCall s em t) :
    WP isa (.call c.name c.code) t (AfterCall s em) :=
  privCall c (privOk_of c hp ha) fun _ hrd' hwr' hsp' hf hpres hvs hpost =>
    afterCall_of c.le c.depth hp ha hrd' hwr' hsp' hf hpres hvs hpost

end VG.Proof.RsaPkcs1Sig.AArch64.Sgn

end

end


/-!
# `vg_rsa_pkcs1_sign` on AArch64: correctness

The encoding into `EM` (`enc_ok`), then zeros to `out` if it fails, or the
private operation on `EM` and zeros to `EM` (`afterEnc_ok`), which is
RFC 8017 §8.2.1 (`signId_eq`); the whole function (`code_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Sign VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.AArch64 (encode psLoop)
open VG.Impl.RsaPkcs1Sig.AArch64.Recover (zeroOut)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov EPre EPost EOut encodeId encode_ok fill_ok clob)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes ne_of_disjoint bytes_apart)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (eval_zero')

theorem signId_eq (nB eB pB qB dPB dQB qInvB : List Byte) (x : BitVec 32) (H : List Byte) :
    Spec.RsaPkcs1Sig.signId nB eB pB qB dPB dQB qInvB x.toNat H =
      match encodeId x H nB.length with
      | some em => Spec.Rsa.privateChecked nB eB em pB qB dPB dQB qInvB
      | none => .invalid := by
  unfold Spec.RsaPkcs1Sig.signId encodeId Spec.RsaPkcs1Sig.sign
  cases Spec.RsaPkcs1Sig.Hash.ofId x.toNat <;> rfl

theorem encodeId_length {x : BitVec 32} {H : List Byte} {k : Nat} {em : List Byte}
    (h : encodeId x H k = some em) : em.length = k := by
  unfold encodeId at h
  split at h
  · exact VG.Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- The hash value, as the entry state gives it. -/
abbrev digest (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat

/-- The encoding of the hash value, from the entry state. -/
def encOut (s : State) : Option (List Byte) :=
  encodeId ((s.gpr .x6).setWidth 32) (digest s) (s.gpr .x3).toNat

/-- The result: the private operation on the encoding, or `invalid`. -/
def sigOut (s : State) : Spec.Rsa.Outcome :=
  match encOut s with
  | some em => privOut s em
  | none => .invalid

/-! ## `Mid` -/

theorem Mid.only {s t w : State} {rs : List Reg} (h : Mid s t) (o : Only rs t w)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid s w where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x19
  hi := fun r hr => (o.gpr _ fun h' => hrs _ h' (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h | h | h | h <;> simp [h])).trans (h.hi r hr)
  v := fun r hr => (o.vcs r hr).trans (h.v r hr)
  sv := by rw [o.mem]; exact h.sv

theorem Mid.frame {s t w : State} {rs : List Reg} {R : Region} (h : Mid s t) (o : Keep rs t w)
    (hm : Frame [R] t.mem w.mem) (hd : Region.Disjoint ⟨fb s + BitVec.ofNat 64 112, 16⟩ R)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid s w :=
  have hw : Mid s { t with gpr := w.gpr, v := w.v } :=
    Mid.only (w := { t with gpr := w.gpr, v := w.v }) h ⟨o.gpr, rfl, rfl, rfl, rfl, o.vcs⟩ hrs
  { hw with
    sp := o.sp.trans h.sp
    rd := o.rd.trans h.rd
    wr := o.wr.trans h.wr
    sv := h.sv.frame_in saved_offs hm fun r hr => by rw [List.mem_singleton.mp hr]; exact hd }

theorem AtEnc.mid {s u : State} (h : AtEnc s u) : Mid s u :=
  ⟨h.sp, h.rd, h.wr, h.x19, fun r hr => h.g r (by revert r; decide), h.v, h.sv⟩

/-! ## The steps -/

theorem enc_ok {K : Nat} {s u : State} (hp : PreS K s) (hu : AtEnc s u) :
    WP isa encode u fun w => Keep clob u w ∧ EOut u w (encOut s) := by
  have hk2 := hp.k2
  obtain hpre : EPre u ((s.gpr .x6).setWidth 32) (s.gpr .x3).toNat := {
    x10 := by rw [hu.x10]; simp
    hk := by rw [hu.x9]
    kle := hk2
    buf := fun i hi => by
      rw [hu.wr, hu.x8, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_frame _ _ (by unfold oEM frameBytes; omega_using [hk2, hi])
    rd := fun j hj => by
      rw [hu.rd, hu.x11]; rw [hu.x12] at hj
      exact Covers.left (Covers.trans (Covers.of_mem fun x hx => by
        rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _ ⟨dR s, List.mem_singleton_self _,
        Offset.contains_base _ (by omega_using [hj]) (by have := hp.wd; omega_using [hj])⟩
    sep := fun j hj i hi => by
      rw [hu.x11, hu.x8]; rw [hu.x12] at hj
      exact ne_of_disjoint (hp.kd.sub_left (em_sub hp)).symm (by have := hp.wd; omega_using []) (by omega_using []) hj hi }
  refine WP.mono (encode_ok hpre) fun w ⟨hK, hout⟩ => ⟨hK, ?_⟩
  obtain hH : Spec.Rsa.bytesAt u.mem (u.gpr .x11) (u.gpr .x12).toNat = digest s := by
    rw [hu.x11, hu.x12]; exact bytes_frame hu.mem hp.kd (by have := hp.wd; omega_using [])
  rw [hH] at hout
  exact hout

/-- Zeros to `out`. -/
theorem zeroSlots_ok {K : Nat} {s u w : State} (hp : PreS K s) (hu : AtEnc s u) (hK : Keep clob u w)
    (hm : w.mem = u.mem) :
    WP isa zeroSlots w fun w' => Mid s w' ∧
      Spec.Rsa.writtenOutcome w'.mem (s.gpr .x0) (s.gpr .x3).toNat ((w'.gpr .x0).setWidth 32) .invalid := by
  obtain hk1 := hp.k1; have hk2 := hp.k2; have hol := hp.ol
  unfold zeroSlots
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_nil ?_)
  obtain O₂ : Only [.x14, .x13] w u₂ := (o₁.trans o₂).mono
  obtain midw : Mid s w := hu.mid.only (Ver.Only.of_keep hK hm)
  refine WP.mono (Rec.zeroOut_ok (p := s.gpr .x0) (n := (s.gpr .x3).toNat) (by omega_using [hk1]) (by omega_using [])
    (by rw [o₂.get .x14, e₁, hK.get .x17, hu.x17])
    (by rw [e₂, o₁.get .x19, midw.x19, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun i hi => by
      rw [O₂.wr, midw.wr]
      exact ⟨_, List.mem_cons_of_mem _ hp.hwo, Offset.contains_base _ (by omega_using [hol, hi]) (by have := hp.wo; omega_using [hi])⟩))
    fun w' ⟨k, mw, x0⟩ => ⟨?_, by rw [x0]; rfl, ?_⟩
  · have fw : Frame [⟨s.gpr .x0, (s.gpr .x3).toNat⟩] u₂.mem w'.mem := by
      rw [mw]; have := frame_writeBytes u₂.mem (s.gpr .x0) (List.replicate (s.gpr .x3).toNat 0)
      rwa [List.length_replicate] at this
    obtain ko' : (kR K s).Disjoint ⟨s.gpr .x0, (s.gpr .x3).toNat⟩ := by rw [← hol]; exact hp.ko
    exact (midw.only O₂).frame k fw (ko'.sub_left (frame_sub K s (d := 112) (n := 16) (by decide)))
  · rw [mw]
    have := bytesAt_writeBytes u₂.mem (s.gpr .x0) (List.replicate (s.gpr .x3).toNat 0) (by simp; omega_using [])
    rwa [List.length_replicate] at this

/-- `EM` overwritten with zeros: `out`, `x0` and `Mid` are kept. -/
theorem wipe_ok {K : Nat} {s t : State} (hp : PreS K s) (hm : Mid s t) :
    WP isa wipe t fun w => Mid s w ∧ w.gpr .x0 = t.gpr .x0 ∧
      Spec.Rsa.bytesAt w.mem (s.gpr .x0) (s.gpr .x3).toNat = Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x3).toNat := by
  obtain hk1 := hp.k1; have hk2 := hp.k2; have hol := hp.ol
  unfold wipe
  refine WP.seq (wp_addSp (by decide) fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ => wp_nil ?_)
  obtain O₃ : Only [.x14, .x13, .x15] t u₃ := (o₁.trans (o₂.trans o₃)).mono
  obtain midu : Mid s u₃ := hm.only O₃
  refine WP.mono (fill_ok (p := fb s + BitVec.ofNat 64 oEM) (n := (s.gpr .x3).toNat) (b := 0) (by omega_using [hk1])
    (by omega_using []) (by rw [o₃.get .x14, o₂.get .x14, e₁, hm.sp]) (by rw [o₃.get .x13, e₂, o₁.get .x19, hm.x19,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [e₃]; rfl) (fun i hi => by
        rw [midu.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        exact in_frame _ _ (by unfold oEM frameBytes; omega_using [hk2, hi]))) fun w ⟨k, mw⟩ => ?_
  obtain fw : Frame [⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .x3).toNat⟩] u₃.mem w.mem := by
    rw [mw]; have := frame_writeBytes u₃.mem (fb s + BitVec.ofNat 64 oEM) (List.replicate (s.gpr .x3).toNat 0)
    rwa [List.length_replicate] at this
  refine ⟨midu.frame k fw (slots_em hp (Nat.le_refl _)), by rw [k.get .x0, O₃.get .x0], ?_⟩
  rw [← O₃.mem]
  obtain ko' : (kR K s).Disjoint ⟨s.gpr .x0, (s.gpr .x3).toNat⟩ := by rw [← hol]; exact hp.ko
  exact bytes_apart (R := ⟨s.gpr .x0, (s.gpr .x3).toNat⟩) fw (ko'.sub_left (em_sub hp)).symm
    (by have := hp.wo; dsimp only; omega_using [])


theorem writtenOutcome_of {m m' : Mem} {out : Addr} {n : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out n = Spec.Rsa.bytesAt m out n) (h : Spec.Rsa.writtenOutcome m out n r o) :
    Spec.Rsa.writtenOutcome m' out n r o := by
  cases o <;> exact ⟨h.1, hb.trans h.2⟩

/-- A call of the private operation from `AtCall` with `n` stack arguments. -/
abbrev CallOk (s : State) (n : Nat) (name : String) (code : Prog isa) : Prop :=
  ∀ em t, AtCall s em t → (∀ i < n, stackArg t i = stackArg s (i + 1)) →
    WP isa (.call name code) t (AfterCall s em)

theorem afterEncN_ok {K n : Nat} {name : String} {priv : Prog isa} {s u w : State} (hp : PreS K s)
    (hA : ArgsOk K s (n + 1)) (hn₁ : 12 ≤ n) (hn₂ : n ≤ 14) (hc : CallOk s n name priv) (hu : AtEnc s u)
    (hK : Keep clob u w) (hout : EOut u w (encOut s)) :
    WP isa (afterEncN n name priv) w fun w' => Mid s w' ∧
      Spec.Rsa.writtenOutcome w'.mem (s.gpr .x0) (s.gpr .x3).toNat ((w'.gpr .x0).setWidth 32) (sigOut s) := by
  unfold afterEncN sigOut
  cases heo : encOut s with
  | none =>
    rw [heo] at hout
    obtain ⟨h0, hm⟩ := hout
    exact WP.ite true ((eval_zero' w .x0).trans (by rw [h0]; rfl)) (fun _ => zeroSlots_ok hp hu hK hm) (by simp)
  | some em =>
    rw [heo] at hout
    obtain ⟨h1, hme⟩ := hout
    refine WP.ite false ((eval_zero' w .x0).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
    refine WP.seq (WP.mono (callArgsN_ok hp hA hn₁ hn₂ hu hK hme (encodeId_length heo)) fun t ht => ?_)
    refine WP.seq (WP.mono (hc em t ht.1 ht.2) fun t' ht' => ?_)
    refine WP.mono (wipe_ok hp ht'.toMid) fun w' ⟨m', x0, hb⟩ => ⟨m', ?_⟩
    rw [x0]; exact writtenOutcome_of hb ht'.res

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
        (by have := saved_offs p hp'; unfold frameBytes; omega_using [this]) (by have := saved_offs p hp'; omega_using [this]))))
    (by rw [o₁.mem]; exact hm.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, fun r hr' => ?_⟩, ?_, ?_⟩
  · simp only [freed]
    by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      exact hr.gpr p hp'
    · have hr'' : r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> first | decide | simp_all [saved]
      obtain h16 : r ∉ [Reg.x16] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'' ⊢
        rcases hr'' with h | h | h | h | h | h | h | h | h <;> subst h <;> decide
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

/-- `vg_rsa_pkcs1_sign`'s result, and the calling convention. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ Spec.Rsa.writtenOutcome s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
    (sigOut s)

theorem codeN_ok {K n : Nat} {name : String} {priv : Prog isa} {s : State} (hp : PreS K s)
    (hA : ArgsOk K s (n + 1)) (hn₁ : 12 ≤ n) (hn₂ : n ≤ 14) (hc : CallOk s n name priv) :
    WP isa (codeN n name priv) s (Post s) := by
  unfold codeN
  refine WP.alloc (by decide) (by have := hp.sp1; unfold stk at this; omega_using [this]) ?_
  unfold bodyN
  refine WP.seq (WP.mono (encArgs_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu => ?_)
  refine WP.seq (WP.mono (enc_ok hp hu) fun w ⟨hK, hout⟩ => ?_)
  refine WP.seq (WP.mono (afterEncN_ok hp hA hn₁ hn₂ hc hu hK hout) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_ok m) fun w ⟨habi, hx0, hmem⟩ => ⟨habi, by rw [hx0, hmem]; exact r⟩

theorem code_ok (c : PrivChecked) {s : State} (hp : PreS c.stack s) :
    WP isa (code c.name c.code) s (Post s) :=
  codeN_ok hp hp.argsOk (by decide) (by decide) fun _ _ ht _ => call_ok c hp ht

end VG.Proof.RsaPkcs1Sig.AArch64.Sgn
