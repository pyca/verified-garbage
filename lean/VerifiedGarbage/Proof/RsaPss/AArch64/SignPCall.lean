module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCall
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCorrect
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTop
import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.RsaPss.AArch64.ByIdx
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.RsaPss.Params

/-!
# RSASSA-PSS signing on AArch64 with the key's precomputed values: the call

`vg_rsa_pss_sign_precomputed` (`signCP`) is `vg_rsa_pss_sign`'s code but for
the call of `vg_rsa_private_checked_precomputed`, whose stack arguments 12 and
13, `pre` and `pre_len` (ours 16 and 17, `PreXS`), are the slots of the
caller's `x19` and `x20`: those registers are restored from them first, and
the restores at the end leave them out (`MidP`). The failures restore them
too (`failP_ok`); `preArgs_ok` and `callP_ok` the call.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp PrivPChecked PrivPOk PrivOk privPCall privRdP privWr preR)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytes_apart)
open VG.Proof.RsaPss.AArch64 (off)

/-- `pre`, our stack arguments 16 and 17. -/
abbrev prR (s : State) : Region := ⟨stackArg s 16, (stackArg s 17).toNat * 8⟩

/-- Our stack arguments, `pre` and `pre_len` included. -/
abbrev aR2 (s : State) : Region := ⟨stackArgAddr s 0, 144⟩

/-- What the code needs of `pre`, by name. -/
structure PreXS (K : Nat) (s : State) : Prop where
  rd : Covers [prR s, aR2 s] s.rd
  sp3 : s.sp.toNat + 144 ≤ 2 ^ 64
  oa : (oR s).Disjoint (aR2 s)
  sa : (sR s).Disjoint (aR2 s)
  ka : (kR K s).Disjoint (aR2 s)
  opr : (oR s).Disjoint (prR s)
  spr : (sR s).Disjoint (prR s)
  kpr : (kR K s).Disjoint (prR s)
  wpr : (stackArg s 16).toNat + (stackArg s 17).toNat * 8 ≤ 2 ^ 64
  prl : (stackArg s 17).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .x3).toNat (s.gpr .x7).toNat (stackArg s 1).toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 16) (stackArg s 17).toNat)

/-- In the frame, after `x19` and `x20` are restored: the slots of the other
saved registers. -/
structure MidP (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  sv : Spill.Saved (fb s) s.gpr (saved.drop 2) t.mem
  x19 : t.gpr .x19 = s.gpr .x19
  x20 : t.gpr .x20 = s.gpr .x20

theorem saved_drop {s : State} {m : Mem} (h : Spill.Saved (fb s) s.gpr saved m) :
    Spill.Saved (fb s) s.gpr (saved.drop 2) m := fun p hp => h p (List.mem_of_mem_drop hp)

/-- `x19` and `x20` restored from their slots. -/
theorem reload_ok {s t : State} (hm : Mid s t) :
    WP isa (.block reload) t fun t' => MidP s t' ∧ t'.gpr .x0 = t.gpr .x0 ∧ t'.mem = t.mem := by
  unfold reload ld
  have rsl : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega)))
  refine wp_ldrSp (by decide) (rsl hm.sp hm.rd hm.wr (by decide)) fun u₁ o₁ e₁ => ?_
  refine wp_ldrSp (by decide) (rsl (o₁.sp.trans hm.sp) (o₁.rd.trans hm.rd) (o₁.wr.trans hm.wr) (by decide))
    fun u₂ o₂ e₂ => wp_nil ?_
  rw [hm.sp, hm.fr.sv (.x19, 96) (by decide)] at e₁
  rw [o₁.sp, hm.sp, o₁.mem, hm.fr.sv (.x20, 104) (by decide)] at e₂
  exact ⟨⟨o₂.sp.trans (o₁.sp.trans hm.sp), o₂.rd.trans (o₁.rd.trans hm.rd), o₂.wr.trans (o₁.wr.trans hm.wr),
      fun r hr => (o₂.vcs r hr).trans ((o₁.vcs r hr).trans (hm.v r hr)),
      by rw [o₂.mem, o₁.mem]; exact saved_drop hm.fr.sv,
      by rw [o₂.gpr .x19 (by decide), e₁], e₂⟩,
    by rw [o₂.gpr .x0 (by decide), o₁.gpr .x0 (by decide)], by rw [o₂.mem, o₁.mem]⟩

/-- Zeros to `out`, 0 returned, and `x19` and `x20` restored. -/
theorem failP_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) (hm : Mid s t)
    (h23 : t.gpr .x23 = s.gpr .x3) :
    WP isa signFailP t fun t' => MidP s t' ∧
      Spec.Rsa.writtenOutcome t'.mem (s.gpr .x0) (s.gpr .x3).toNat ((t'.gpr .x0).setWidth 32) .invalid :=
  WP.seq (WP.mono (fail_ok hp hm h23) fun _ ⟨m, r⟩ =>
    WP.mono (reload_ok m) fun _ ⟨m', h0, hmem⟩ => ⟨m', by rw [h0, hmem]; exact r⟩)

/-- At the call of `vg_rsa_private_checked_precomputed`. -/
structure AtCallP (K : Nat) (s : State) (em : List Byte) (t : State) : Prop extends CallArgs s t where
  pre : stackArg t 12 = stackArg s 16
  prl : stackArg t 13 = stackArg s 17
  x19 : t.gpr .x19 = s.gpr .x19
  x20 : t.gpr .x20 = s.gpr .x20
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame (wrS K s) s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr (saved.drop 2) t.mem
  em : Spec.Rsa.bytesAt t.mem (off (scr s) oEm) (s.gpr .x3).toNat = em

/-- Our stack argument `j < 18`, in memory changed only where the code
writes. -/
theorem argP_frameW {K : Nat} {s : State} (hx : PreXS K s) {m : Mem}
    (h : Frame (wrS K s) s.mem m) {j : Nat} (hj : j < 18) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR2 s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by have := hx.sp3; omega))
    (wrS_disj hx.ka hx.sa.symm) (by decide)

theorem argP_in {K : Nat} {s : State} (hx : PreXS K s) {rs : List Region} (hrd : Covers s.rd rs) {j : Nat}
    (hj : j < 18) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hx.rd _ _ ⟨aR2 s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by have := hx.sp3; omega)⟩

/-- `x19` and `x20` restored, and `pre` and `pre_len` in their slots. -/
theorem preArgs_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) (hx : PreXS K s)
    {em : List Byte} (ha : AtCall K s em t) : WP isa (.block preArgs) t (AtCallP K s em) := by
  unfold preArgs reload st ld arg
  simp only [List.cons_append, List.nil_append]
  have rsl : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega)))
  have hA : ∀ {u : State} (j : Nat), j < 18 → u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * j)) 8 := fun j hj hsp hrd hwr => by
    rw [hsp, hrd, ← stackArgAddr_fb]
    exact argP_in hx (Covers.left (Covers.refl _)) hj
  -- `x19`, `x20`.
  refine wp_ldrSp (by decide) (rsl ha.sp ha.rd ha.wr (by decide)) fun u₁ o₁ e₁ => ?_
  rw [ha.sp, ha.fr.sv (.x19, 96) (by decide)] at e₁
  refine wp_ldrSp (by decide) (rsl (o₁.sp.trans ha.sp) (o₁.rd.trans ha.rd) (o₁.wr.trans ha.wr) (by decide))
    fun u₂ o₂ e₂ => ?_
  rw [o₁.sp, ha.sp, o₁.mem, ha.fr.sv (.x20, 104) (by decide)] at e₂
  have sp₂ : u₂.sp = fb s := o₂.sp.trans (o₁.sp.trans ha.sp)
  have rd₂ : u₂.rd = s.rd := o₂.rd.trans (o₁.rd.trans ha.rd)
  have wr₂ : u₂.wr = ⟨fb s, frameBytes⟩ :: s.wr := o₂.wr.trans (o₁.wr.trans ha.wr)
  have mem₂ : u₂.mem = t.mem := o₂.mem.trans o₁.mem
  -- `pre`.
  refine wp_ldrSp (by decide) (hA 16 (by decide) sp₂ rd₂ wr₂) fun u₃ o₃ e₃ => ?_
  rw [sp₂, ← stackArgAddr_fb, mem₂, argP_frameW hx ha.mem (by decide)] at e₃
  refine wp_addSp (by decide) fun u₄ o₄ e₄ => ?_
  rw [o₃.sp, sp₂, BitVec.add_zero] at e₄
  refine wp_strx (a := fb s + BitVec.ofNat 64 96) (by decide) (by rw [e₄])
    (by rw [o₄.wr, o₃.wr, wr₂]; exact in_frame _ _ (by decide)) fun u₅ m₅ => ?_
  have sp₅ : u₅.sp = fb s := by rw [m₅.sp, o₄.sp, o₃.sp, sp₂]
  have rd₅ : u₅.rd = s.rd := by rw [m₅.rd, o₄.rd, o₃.rd, rd₂]
  have wr₅ : u₅.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₅.wr, o₄.wr, o₃.wr, wr₂]
  have mem₅ : u₅.mem = t.mem.writeW (fb s + BitVec.ofNat 64 96) (stackArg s 16) := by
    rw [m₅.mem, o₄.get .x9, e₃, o₄.mem, o₃.mem, mem₂]
  -- `pre_len`.
  refine wp_ldrSp (by decide) (hA 17 (by decide) sp₅ rd₅ wr₅) fun u₆ o₆ e₆ => ?_
  have c96 : (⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region).Contains (fb s + BitVec.ofNat 64 96) 8 :=
    Offset.contains _ (by decide) (by decide) (by decide)
  have c104 : (⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region).Contains (fb s + BitVec.ofNat 64 104) 8 :=
    Offset.contains _ (by decide) (by decide) (by decide)
  have dA : (aR2 s).Disjoint ⟨fb s + BitVec.ofNat 64 96, 16⟩ :=
    (hx.ka.sub_left (frame_sub K s (d := 96) (n := 16) (by decide))).symm
  have f5 : Frame [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)] t.mem u₅.mem := by
    rw [mem₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c96
  have c17 : (aR2 s).Contains (stackArgAddr s 17) 8 := by
    rw [stackArgAddr_eq s 17]
    exact Offset.contains_base _ (by decide) (by have := hx.sp3; omega)
  have m17 : u₅.mem.readW (stackArgAddr s 17) 64 = stackArg s 17 := by
    rw [f5.readW c17 (fun r hr => by rw [List.mem_singleton.mp hr]; exact dA) (by decide)]
    exact argP_frameW hx ha.mem (by decide)
  rw [sp₅, ← stackArgAddr_fb, m17] at e₆
  refine wp_addSp (by decide) fun u₇ o₇ e₇ => ?_
  rw [o₆.sp, sp₅, BitVec.add_zero] at e₇
  refine wp_strx (a := fb s + BitVec.ofNat 64 104) (by decide) (by rw [e₇])
    (by rw [o₇.wr, o₆.wr, wr₅]; exact in_frame _ _ (by decide)) fun u₈ m₈ => wp_nil ?_
  have mem₈ : u₈.mem = (t.mem.writeW (fb s + BitVec.ofNat 64 96) (stackArg s 16)).writeW
      (fb s + BitVec.ofNat 64 104) (stackArg s 17) := by
    rw [m₈.mem, o₇.get .x9, e₆, o₇.mem, o₆.mem, mem₅]
  have fW : Frame [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)] t.mem u₈.mem := by
    rw [mem₈]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c96).writeW (List.mem_singleton_self _) _ c104
  have r96 : ∀ {d : Nat}, d + 8 ≤ 96 ∨ 112 ≤ d → d + 8 ≤ frameBytes →
      u₈.mem.readW (fb s + BitVec.ofNat 64 d) 64 = t.mem.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd hd' =>
    fW.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega) (by unfold frameBytes at hd'; omega) (by decide)) (by decide)
  have gO : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x9 → r ≠ .x16 → u₈.gpr r = t.gpr r := fun r h1 h2 h3 h4 => by
    rw [m₈.gpr, o₇.gpr r (by simpa using h4), o₆.gpr r (by simpa using h3), m₅.gpr, o₄.gpr r (by simpa using h4),
      o₃.gpr r (by simpa using h3), o₂.gpr r (by simpa using h2), o₁.gpr r (by simpa using h1)]
  have sp₈ : u₈.sp = fb s := by rw [m₈.sp, o₇.sp, o₆.sp, sp₅]
  have hst : ∀ i, u₈.mem.readW (u₈.sp + BitVec.ofNat 64 (8 * i)) 64 = stackArg u₈ i := fun _ => rfl
  refine {
    sp := sp₈
    rd := (by rw [m₈.rd, o₇.rd, o₆.rd, rd₅])
    wr := (by rw [m₈.wr, o₇.wr, o₆.wr, wr₅])
    x0 := (by rw [gO .x0 (by decide) (by decide) (by decide) (by decide), ha.x0])
    x1 := (by rw [gO .x1 (by decide) (by decide) (by decide) (by decide), ha.x1])
    x2 := (by rw [gO .x2 (by decide) (by decide) (by decide) (by decide), ha.x2])
    x3 := (by rw [gO .x3 (by decide) (by decide) (by decide) (by decide), ha.x3])
    x4 := (by rw [gO .x4 (by decide) (by decide) (by decide) (by decide), ha.x4])
    x5 := (by rw [gO .x5 (by decide) (by decide) (by decide) (by decide), ha.x5])
    x6 := (by rw [gO .x6 (by decide) (by decide) (by decide) (by decide), ha.x6])
    x7 := (by rw [gO .x7 (by decide) (by decide) (by decide) (by decide), ha.x7])
    args := fun i hi => ?_
    pre := ?_
    prl := ?_
    x19 := (by rw [m₈.gpr, o₇.gpr .x19 (by decide), o₆.gpr .x19 (by decide), m₅.gpr, o₄.gpr .x19 (by decide),
      o₃.gpr .x19 (by decide), o₂.gpr .x19 (by decide), e₁])
    x20 := (by rw [m₈.gpr, o₇.gpr .x20 (by decide), o₆.gpr .x20 (by decide), m₅.gpr, o₄.gpr .x20 (by decide),
      o₃.gpr .x20 (by decide), e₂])
    v := fun r hr => (by
      rw [m₈.vcs r hr, o₇.vcs r hr, o₆.vcs r hr, m₅.vcs r hr, o₄.vcs r hr, o₃.vcs r hr, o₂.vcs r hr,
        o₁.vcs r hr, ha.v r hr])
    mem := ha.mem.trans (fW.sub fun r hr => (by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨fb s, frameBytes⟩, List.mem_cons_self, Offset.sub_base _ (by decide)⟩))
    sv := fun p hp' => (by
      have := saved_offs p (List.mem_of_mem_drop hp')
      have h112 : 112 ≤ p.2 := (show ∀ q ∈ saved.drop 2, 112 ≤ q.2 by decide) p hp'
      rw [r96 (.inr h112) (by unfold frameBytes; omega)]
      exact ha.fr.sv p (List.mem_of_mem_drop hp'))
    em := ?_ }
  · show u₈.mem.readW (u₈.sp + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [sp₈, r96 (.inl (by omega)) (by unfold frameBytes; omega)]
    have := ha.args i hi
    simp only [stackArg, stackArgAddr, ha.sp] at this
    exact this
  · show u₈.mem.readW (u₈.sp + BitVec.ofNat 64 (8 * 12)) 64 = _
    rw [sp₈, mem₈, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · show u₈.mem.readW (u₈.sp + BitVec.ofNat 64 (8 * 13)) 64 = _
    rw [sp₈, mem₈, Mem.readW_writeW_self64]
  · rw [← ha.em]
    have hemR : (kR K s).Disjoint ⟨off (scr s) oEm, (s.gpr .x3).toNat⟩ := hp.ks.sub_right (em_sub hp)
    exact bytes_apart (R := ⟨off (scr s) oEm, (s.gpr .x3).toNat⟩) fW
      (hemR.symm.sub_right (frame_sub K s (d := 96) (n := 16) (by decide))) (by dsimp only; omega_using [])


/-! ## The call -/

theorem privArgsP_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) (hx : PreXS K s)
    {em : List Byte} (hm : Main K s em t) : WP isa (.block privArgsP) t (AtCallP K s em) := by
  unfold privArgsP
  rw [WP.block_append_iff]
  exact WP.mono (privArgs_ok hp hm) fun _ h => preArgs_ok hp hx h

/-- `pre`'s words are few. -/
theorem prl_le {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) (hx : PreXS K s) : (stackArg s 17).toNat ≤ 1024 := by
  have := hp.k2; have := hp.p2; have := hp.q2
  rw [hx.prl]
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords]
  omega

theorem privPOk_ofP (c : PrivPChecked) {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s)
    (hx : PreXS K s) (hcK : c.stack ≤ K) {em : List Byte} (ha : AtCallP K s em t) : PrivPOk c.stack t := by
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hcl := c.le
  have hK : Region.Sub ⟨fb s - BitVec.ofNat 64 c.stack, c.stack⟩ (kR K s) := fun a h =>
    (Offset.sub_below (fb s) (a := c.stack) (b := K) (n := c.stack) (m := K) hcK (by omega_using [hcK]) a h) |>
      fun h' => by
        have e : fb s - BitVec.ofNat 64 K = kb K s := by rw [fb_eq K, BitVec.add_sub_cancel]
        rw [e] at h'
        exact Region.sub_prefix (by unfold stk; omega_using []) a h'
  have a1 : stackArg t 1 = s.gpr .x7 := ha.args 1 (by decide)
  have a3 : stackArg t 3 = stackArg s 1 := ha.args 3 (by decide)
  have a0 : stackArg t 0 = s.gpr .x6 := ha.args 0 (by decide)
  have a2 : stackArg t 2 = stackArg s 0 := ha.args 2 (by decide)
  have a10 : stackArg t 10 = off (scr s) oRsa := ha.args 10 (by decide)
  have a11 : stackArg t 11 = stackArg s 13 - BitVec.ofNat 64 1024 := ha.args 11 (by decide)
  have hO : (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = oR s := by
    show (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    rw [hp.ol]
  have f112 : Region.Sub ⟨fb s, 112⟩ (kR K s) := by
    have := frame_sub K s (d := 0) (n := 112) (by decide); rwa [BitVec.add_zero] at this
  have hP : preR t = prR s := by simp only [preR, ha.pre, ha.prl]
  have hw : 8 * (stackArg s 17).toNat < 2 ^ 64 := by have := prl_le hp hx; omega
  have hpre : Spec.Rsa.wordsAt t.mem (stackArg s 16) (stackArg s 17).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 16) (stackArg s 17).toNat :=
    VG.Proof.Rsa.wordsAt_frame ha.mem hw (wrS_disj (by rw [Nat.mul_comm]; exact hx.kpr)
      (by rw [Nat.mul_comm]; exact hx.spr.symm))
  have hl : ∀ {p : Addr} {len : Nat}, p.toNat + len ≤ 2 ^ 64 → len ≤ 2 ^ 64 := fun h => by omega_using [h]
  refine ⟨privOk_of c hp hcK ha.toCallArgs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha.sp]; have := hfb; unfold frameBytes at this; omega
  · rw [ha.x0, ha.x1, ha.sp, hO]; exact (hp.ko.sub_left f112).symm
  · rw [a10, a11, ha.sp]; exact (hp.ks.sub_left f112).symm.sub_left (sc_sub hp)
  · rw [ha.sp]; exact (Offset.base_disjoint_below (fb s) (n := c.stack) (k := 112) (by omega_using [hcl])).symm
  · rw [hP, ha.x0, ha.x1, hO]; exact hx.opr
  · rw [hP, a10, a11]; exact hx.spr.sub_left (sc_sub hp)
  · rw [hP, ha.sp]; exact hx.kpr.sub_left hK
  · rw [ha.pre, ha.prl]; exact hx.wpr
  · rw [hP, ha.sp, ha.rd]
    refine Covers.cons (Covers.left (Covers.trans (Covers.one ⟨prR s, by simp, Region.contains_self _ _⟩) hx.rd))
      (Covers.right (Covers.one ?_))
    rw [ha.wr]
    exact in_frame s s.wr (d := 0) (n := 112) (by decide) |> fun h => by simpa using h
  · rw [ha.prl, ha.x3, a1, a3]; exact hx.prl
  · rw [ha.x2, ha.x3, a0, a1, a2, a3, ha.pre, ha.prl, hpre,
      bytes_wrS ha.mem hp.kn hp.ns (hl hp.wn), bytes_wrS ha.mem hp.kp hp.ps (hl hp.wp),
      bytes_wrS ha.mem hp.kq hp.qs (hl hp.wq)]
    exact hx.key

/-- After the call: `MidP`, and `out` written with the result. -/
structure AfterCallP (s : State) (em : List Byte) (t : State) : Prop extends MidP s t where
  res : Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (privOut s em)

theorem callP_ok (c : PrivPChecked) {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s)
    (hx : PreXS K s) (hcK : c.stack ≤ K) {em : List Byte} (ha : AtCallP K s em t) :
    WP isa (.call c.name c.code) t (AfterCallP s em) := by
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hcl := c.le
  have hd := c.depth
  have a1 : stackArg t 1 = s.gpr .x7 := ha.args 1 (by decide)
  have a0 : stackArg t 0 = s.gpr .x6 := ha.args 0 (by decide)
  have a2 : stackArg t 2 = stackArg s 0 := ha.args 2 (by decide)
  have a3 : stackArg t 3 = stackArg s 1 := ha.args 3 (by decide)
  have a4 : stackArg t 4 = stackArg s 2 := ha.args 4 (by decide)
  have a6 : stackArg t 6 = stackArg s 4 := ha.args 6 (by decide)
  have a8 : stackArg t 8 = stackArg s 6 := ha.args 8 (by decide)
  have a10 : stackArg t 10 = off (scr s) oRsa := ha.args 10 (by decide)
  have a11 : stackArg t 11 = stackArg s 13 - BitVec.ofNat 64 1024 := ha.args 11 (by decide)
  refine privPCall c (privPOk_ofP c hp hx hcK ha) fun s' hrd' hwr' hsp' hf hpres hvs hpost => ?_
  simp only [privWr] at hf
  rw [ha.x0, ha.x1, a10, a11, ha.sp] at hf
  have hl : ∀ {p : Addr} {len : Nat}, p.toNat + len ≤ 2 ^ 64 → len ≤ 2 ^ 64 := fun h => by omega_using [h]
  rw [ha.x0, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, a0, a1, a2, a3, a4, a6, a8, ha.em,
    bytes_wrS ha.mem hp.kn hp.ns (hl hp.wn), bytes_wrS ha.mem hp.ke hp.es (hl hp.we),
    bytes_wrS ha.mem hp.kp hp.ps (hl hp.wp), bytes_wrS ha.mem hp.kq hp.qs (hl hp.wq),
    bytes_wrS ha.mem (len := (s.gpr .x7).toNat) (by rw [← hp.hdp]; exact hp.kdp) (by rw [← hp.hdp]; exact hp.dps)
      (by have := hp.wdp; rw [hp.hdp] at this; omega_using []),
    bytes_wrS ha.mem (len := (stackArg s 1).toNat) (by rw [← hp.hdq]; exact hp.kdq)
      (by rw [← hp.hdq]; exact hp.dqs) (by have := hp.wdq; rw [hp.hdq] at this; omega_using []),
    bytes_wrS ha.mem (len := (s.gpr .x7).toNat) (by rw [← hp.hqi]; exact hp.kqi) (by rw [← hp.hqi]; exact hp.qis)
      (by have := hp.wqi; rw [hp.hqi] at this; omega_using [])] at hpost
  have hO : (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = oR s := by
    show (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    rw [hp.ol]
  have f72 : Region.Sub ⟨fb s + BitVec.ofNat 64 112, 72⟩ (kR K s) := frame_sub K s (by decide)
  exact {
    sp := hsp'.trans ha.sp
    rd := hrd'.trans ha.rd
    wr := hwr'.trans ha.wr
    v := fun r hr => (hvs r hr).trans (ha.v r hr)
    sv := ha.sv.frame_in (lo := 112) (n := 72) (by decide) hf (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · rw [hO]; exact hp.ko.sub_left f72
      · exact (hp.ks.sub_left f72).sub_right (sc_sub hp)
      · exact Offset.disjoint_below _ (by omega_using [hcl, hd]))
    x19 := (hpres .x19 (by decide) (by decide)).trans ha.x19
    x20 := (hpres .x20 (by decide) (by decide)).trans ha.x20
    res := hpost }


/-! ## The function -/

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PrivPChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Proof.RsaPss.AArch64 (ebV byIdx_wp Tabs restoreP_frame_ok)

include h624 hcK in
theorem mainP_ok {s u : State} (hp : PreS tsH tsG K s) (hx : PreXS K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) (hu : AtChk s u) (hsy : u.syms = s.syms) (h0 : s.mem (s.gpr .x2) ≠ 0) :
    WP isa (seqs [.block (emBitsB ++ encArgs), byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs,
      .ite (.zero .w .x0) signFailP (.seq (.block privArgsP) (.call c.name c.code))]) u fun t => MidP s t ∧
      Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (signOut Hs Gs s) := by
  have hk1 := hp.k1
  obtain ⟨heb1, heb2, hlok, -⟩ := eb_bounds hp h0
  have hsign := signOut_enc Hs Gs (s := s) (by omega) h0
  unfold seqs seqs
  refine WP.seq (WP.mono_syms (args_ok hp h0 hu) fun t ht sy => ?_)
  refine WP.seq (byIdx_wp E.mem (fun j hj => by unfold idxs at hj; simp at hj; omega) (ht.x27.trans E.idx)
    fun t' o sy' => WP.mono (encCall_ok hp h624 E (ht.only9 o) (by rw [sy', sy, hsy]) (by omega) rfl heb1 heb2)
      fun t₂ ht₂ => ?_)
  unfold seqs
  have M₂ : Mid s t₂ := ⟨ht₂.sp, ht₂.rd, ht₂.wr, ht₂.v, ht₂.fr⟩
  refine WP.ite _ (eval_zero_w _ _) (fun hb => ?_) (fun hb => ?_)
  · refine WP.mono (failP_ok hp M₂ ht₂.x23) fun t' ⟨m, r⟩ => ⟨m, ?_⟩
    rw [hsign]
    have hres := ht₂.res
    revert hres
    cases Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat) (ebS s) with
    | none => intro _; exact r
    | some e' =>
      intro hres
      rw [hres.1] at hb
      exact absurd hb (by decide)
  obtain ⟨e', he', hm⟩ := main_of hp h0 ht₂ (by rw [eval_zero_w, ← hb])
  refine WP.seq (WP.mono (privArgsP_ok hp hx hm) fun u₃ h₃ => ?_)
  refine WP.mono (callP_ok c hp hx hcK h₃) fun t' ht' => ⟨ht'.toMidP, ?_⟩
  rw [hsign]
  erw [he']
  exact ht'.res

include h624 hcK in
theorem bodyP_ok {s u : State} (hp : PreS tsH tsG K s) (hx : PreXS K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) (hu : AtChk s u) (hsy : u.syms = s.syms) :
    WP isa (.ite (.zero .x .x10) signFailP (seqs [.block (emBitsB ++ encArgs),
      byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs,
      .ite (.zero .w .x0) signFailP (.seq (.block privArgsP) (.call c.name c.code))])) u fun t => MidP s t ∧
      Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (signOut Hs Gs s) := by
  have hk1 := hp.k1
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x2)).toNat := by rw [hu.x10, setWidth_byte]
  refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have h0 : s.mem (s.gpr .x2) = 0 := by
      rw [hx10, beq_iff_eq] at hb
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hb
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .x2)).isLt; omega)] at this
      exact this
    exact WP.mono (failP_ok hp ⟨hu.sp, hu.rd, hu.wr, hu.v, hu.fr⟩ hu.x23) fun t ⟨m, r⟩ =>
      ⟨m, by rw [signOut_zero Hs Gs (by omega) h0]; exact r⟩
  have h0 : s.mem (s.gpr .x2) ≠ 0 := fun h => by rw [hx10, h] at hb; exact absurd hb (by decide)
  exact mainP_ok c h624 hcK hp hx E hu hsy h0

include h624 hcK in
theorem codeP_ok {s : State} (hp : PreS tsH tsG K s) (hx : PreXS K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) :
    WP isa (signCP f g c.name c.code) s (Post Hs Gs s) := by
  unfold signCP
  refine WP.alloc (by decide) (by have := fb_toNat hp; omega) ?_
  unfold signCBodyP seqs seqs seqs
  refine WP.seq (WP.mono_syms (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu sy => ?_)
  refine WP.seq (WP.mono (bodyP_ok c h624 hcK hp hx E hu (by rw [sy]; simp [allocated])) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restoreP_frame_ok m.sp m.wr m.v m.sv m.x19 m.x20) fun w ⟨habi, hx0, hmem⟩ =>
    ⟨habi, by rw [hx0, hmem]; exact r⟩

end

end VG.Proof.RsaPss.AArch64.Sgn
