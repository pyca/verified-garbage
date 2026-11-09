module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkFixedSaltCT
import VerifiedGarbage.Proof.RsaPss.AArch64.ChkTop
import VerifiedGarbage.Proof.RsaPss.AArch64.EncCT
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyParts
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.RsaPss.AArch64.ChkFixedSaltCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.ChkTop
meta import VerifiedGarbage.Proof.RsaPss.AArch64.EncCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
meta import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyParts
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp

/-!
# EMSA-PSS's check of an encoding on AArch64: constant time

`code_ct`: two runs of `checkEncoding` from entry states with the same
public data leak the same trace. The prologue, the copy of the encoding and
the checks of the lengths branch and address memory by the lengths only (the
taint analysis, and correctness for the branches and for `any_salt_len`,
loaded from its slot: `expLen_ct`); verification's checks are `check_ct`,
from the registers and slots the anchor fixes (`vr_of`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite two_alloc wp_ldrSp)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off two_taintE two_step pins_nil zH PssChecks fitH_ok saltFitsR_ok expLen_ok
  dbRegs_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb)
open VG.Proof.RsaPss.AArch64.Enc (ret0_ct)

/-- After the checks of the lengths. -/
structure AtS (D : Nat) (s w : State) : Prop where
  c : AtCT s w
  em : ∀ i < (s.gpr .x2).toNat, w.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0
  x9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x2).toNat - (D + 2))
  x10 : (w.gpr .x10 != 0) = decide ((s.gpr .x2).toNat - (D + 2) <
    (if anyC s = 0 then s.gpr .x4 else 0).toNat)
  hk : ¬ (s.gpr .x2).toNat < D + 2

/-- `expLen`: `any_salt_len` is loaded from its slot, and branched on. -/
theorem expLen_ct {T : Tabs} {Φ : State → State → Prop} (hΦ : ∀ a u, Φ a u → ∃ s, E T a s ∧ AtC s u) :
    RelCT isa (Two Φ) expLen (Two fun a t => t.sp = fb a) := by
  refine two_post ?_ fun a u h => by
    obtain ⟨s, e, hu⟩ := hΦ a u h
    exact WP.mono (expLen_ok (lay_of e.1 hu.sp hu.x20 hu.wr) hu.fr.any hu.fr.sl) fun t ⟨O, _⟩ => by
      rw [O.sp, hu.sp, e.fb]
  unfold expLen
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → t.sp = fb a) → Pins Φ [] := fun h =>
    pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h a s₁ h₁, h a s₂ h₂]
  refine two_step (Ψ := fun a t => t.sp = fb a ∧ t.gpr .x13 = anyC a)
    (two_taint [] (pin fun a t h => by obtain ⟨s, e, hu⟩ := hΦ a t h; rw [hu.sp, e.fb]) (by taint_decide))
    (fun a u h => ?_) ?_
  · obtain ⟨s, e, hu⟩ := hΦ a u h
    unfold ld
    have hin : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 sAny) 8 := by
      rw [hu.sp, hu.rd, hu.wr]
      exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide)))
    refine wp_ldrSp (by decide) hin fun u' o x => wp_nil ⟨by rw [o.sp, hu.sp, e.fb], ?_⟩
    rw [x, hu.sp]; exact hu.fr.any.trans e.any
  refine two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
    (two_taint [] (pin fun a t h => h.1.1) (by taint_decide)) (two_taint [] (pin fun a t h => h.1.1) (by taint_decide))

/-- After `dbRegs`: the checks' start. -/
theorem vr_of {T : Tabs} {a s t : State} (ok : VOk T.H.D a) (e : E T a s) (htt : AtCT s t)
    (h24 : t.gpr .x24 = off (s.gpr .x6) (oEm + 0)) (h25 : t.gpr .x25 = BitVec.ofNat 64 (dbA T.H.D s)) :
    VR T T.H.D (vregs T.H.D) vslots a t := by
  have ht := htt.e
  have L := lay_of e.1 ht.sp ht.x20 ht.wr
  rw [e.fb, show s.gpr .x6 = scr a from e.scr] at L
  have h2 := e.gpr (r := .x2) (by decide)
  refine ⟨⟨s, t, e, htt, Frame.refl _ _, rfl, ht.rd, ht.wr⟩, L, fun q hq => ?_, fun q hq => ?_, ok, rfl⟩
  · simp only [vregs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [ht.x19]; exact congrArg (off · oSt) e.scr
    · rw [ht.x21]; exact congrArg (off · oDig) e.scr
    · rw [ht.x23, h2]
    · rw [h24]; exact congrArg (off · (oEm + 0)) e.scr
    · rw [h25]; show BitVec.ofNat 64 ((s.gpr .x2).toNat - 0 - T.H.D - 1) = BitVec.ofNat 64 ((a.gpr .x2).toNat - 0 - T.H.D - 1)
      rw [h2]
  · simp only [vslots, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [← e.fb]; exact ht.lo
    · rw [← e.fb]; exact ht.c.trans (by show (cC s).setWidth 64 = (cC a).setWidth 64; rw [cC, cC, e.z])
    · rw [← e.fb]; exact ht.fr.any.trans e.any
    · rw [← e.fb]; exact ht.fr.sl.trans (e.gpr (by decide))
    · rw [← e.fb]; exact ht.fr.dig.trans (e.gpr (by decide))

section
variable {T : Tabs} (hH : HashOK T.H) (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK T.G)
  {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = T.G.D)
  (hGv : Proof.Mgf1.Valid Gs) (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P)

include hH hGh hGl hGv hc hdo in
theorem main_ct :
    RelCT isa (Two fun a w => (∃ s, E T a s ∧ AtS T.H.D s w) ∧ isa.eval (.nonzero .x .x10) w = some false)
      (chkMain T.f T.H T.g) (Two fun a t => t.sp = fb a) := by
  show RelCT isa _ (.seq (.block dbRegs) (seqs [.block acc0, mgfXor T.H T.g, .block clearTop, posScan, posCheck,
    FixedSalt.select T.f T.H])) _
  refine RelCT.seq (two_post (Ψ := VR T T.H.D (vregs T.H.D) vslots)
    (two_taint [] (fun a w₁ w₂ ⟨⟨s₁, h₁, j₁⟩, _⟩ ⟨⟨s₂, h₂, j₂⟩, _⟩ =>
      ⟨by rw [j₁.c.e.sp, j₂.c.e.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a w ⟨⟨s, e, hS⟩, hcond⟩ => ?_) (check_ct hH hGm hGh hGl hGv hc hdo)
  have hk := hS.hk
  have hp := e.1
  have hk1 := hp.k1; have hk2 := hp.k2
  have h2 := e.gpr (r := .x2) (by decide)
  have ok : VOk T.H.D a := by
    refine ⟨?_, ?_, ?_, Nat.zero_le 1, ?_⟩
    · show 1 ≤ (a.gpr .x2).toNat; rw [← h2]; exact hk1
    · show (a.gpr .x2).toNat ≤ 1024; rw [← h2]; exact hk2
    · show T.H.D + 2 ≤ (a.gpr .x2).toNat - 0; rw [← h2]; omega
    · intro ha
      have hb := hS.x10
      have he : anyC s = 0 := e.any.trans ha
      rw [eval_nonzero] at hcond
      rw [Option.some.inj hcond, ite_eq_left he] at hb
      have hn := of_decide_eq_false hb.symm
      show (a.gpr .x4).toNat < (a.gpr .x2).toNat - 0 - T.H.D - 1
      rw [← e.gpr (r := .x4) (by decide), ← h2]
      omega
  refine WP.mono_syms (dbRegs_ok (lay_of hp hS.c.e.sp hS.c.e.x20 hS.c.e.wr) hS.x9 hS.c.e.lo)
    fun u ⟨O, x25, x24⟩ sy => vr_of ok e (hS.c.only O sy) x24 (by
      rw [x25]; show _ = BitVec.ofNat 64 ((s.gpr .x2).toNat - 0 - T.H.D - 1); congr 1; omega)

include hH hGh hGl hGv hc hdo in
theorem code_ct : RelCT isa (Two (E T)) (checkEncoding T.f T.H T.g) fun _ _ => True := by
  have hD : T.H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega
  unfold checkEncoding
  refine two_alloc (R := fun _ _ => True) ?_
  unfold chkBody seqs seqs seqs seqs
  rw [show chkPrologue ++ tabSlots = (chkPrologue ++ [arg .x9 0]) ++ tabSlots.tail from rfl]
  refine RelCT.seq_block_append ?_
  -- The prologue.
  refine RelCT.seq (two_post (Ψ := fun a u₁ => ∃ s u, E T a s ∧ AtC s u ∧ Only [.x9] u u₁ ∧
      u₁.gpr .x9 = stackArg s 0 ∧ u₁.syms = s.syms)
    (two_taint [] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.2.1.sp, h₂.2.1.sp],
        fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    rw [WP.block_append_iff]
    exact WP.mono_syms (prologue_ok h.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun t ht sy =>
      WP.mono_syms (arg0_ok h.1 ht) fun u₁ ⟨o, e9⟩ sy' => ⟨s, t, h, ht, o, e9, sy'.trans sy⟩
  -- The tables' words.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, E T a s ∧ AtCT s u)
    (two_taint [.x9] (fun _ u₁ u₂ ⟨s₁, v₁, h₁, j₁, o₁, x₁, _⟩ ⟨s₂, v₂, h₂, j₂, o₂, x₂, _⟩ =>
        ⟨by rw [o₁.sp, o₂.sp, j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => by
          rw [List.mem_singleton.mp hr, x₁, x₂, h₁.arg (by decide), h₂.arg (by decide)]⟩) (by taint_decide))
    fun a u₁ ⟨s, u, h, hu, o, e9, sy⟩ => WP.mono (tabSlotsT_ok h.1 hu o e9 sy) fun t ht => ⟨s, h, ht⟩) ?_
  -- The copy.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, E T a s ∧ AtCT s u ∧
      ∀ i < (s.gpr .x2).toNat, u.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0)
    (two_taint [.x1, .x20, .x23] (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => ⟨by rw [j₁.e.sp, j₂.e.sp, h₁.fb, h₂.fb],
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [j₁.e.x1, j₂.e.x1, h₁.gpr (by decide), h₂.gpr (by decide)]
        · rw [j₁.e.x20, j₂.e.x20, h₁.gpr (by decide), h₂.gpr (by decide)]
        · rw [j₁.e.x23, j₂.e.x23, h₁.gpr (by decide), h₂.gpr (by decide)]⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => WP.mono_syms (copyIn_okC h.1 hu.e) fun t ⟨ht, hem, hf⟩ sy =>
      ⟨s, h, hu.of h.1 ht hf sy, hem⟩) ?_
  -- `fitH`.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, E T a s ∧ AtCT s u ∧
      (∀ i < (s.gpr .x2).toNat, u.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0) ∧
      u.gpr .x9 = BitVec.ofNat 64 (s.gpr .x2).toNat ∧ (u.gpr .x10 != 0) = decide ((s.gpr .x2).toNat < T.H.D + 2))
    (two_taintE [] (fun _ _ _ ⟨s₁, h₁, j₁, _⟩ ⟨s₂, h₂, j₂, _⟩ => ⟨by rw [j₁.e.sp, j₂.e.sp, h₁.fb, h₂.fb],
        fun _ h => absurd h List.not_mem_nil⟩)
      (c' := Code.eraseOff (.block (fitH zH))) rfl (by taint_decide))
    fun a u ⟨s, h, hu, hem⟩ => ?_) ?_
  · have hk2 := h.1.k2
    exact WP.mono_syms (fitH_ok T.H hD (k := (s.gpr .x2).toNat)
      (by rw [hu.e.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)) fun t ⟨O, x9, x10⟩ sy =>
      ⟨s, h, hu.only O sy, fun i hi => by rw [O.mem]; exact hem i hi, x9, x10⟩
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, _, _, _, x₁⟩ ⟨s₂, h₂, _, _, _, x₂⟩ => by
      rw [eval_nonzero, eval_nonzero, x₁, x₂, h₁.gpr (r := .x2) (by decide), h₂.gpr (r := .x2) (by decide)])
    (ret0_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => by rw [j.e.sp, h.fb]) ?_
  refine RelCT.assoc (RelCT.seq (two_post (Ψ := fun a w => ∃ s, E T a s ∧ AtS T.H.D s w)
    (RelCT.seq (expLen_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => ⟨s, h, j.e⟩) (two_taintE [] (fun a t₁ t₂ h₁ h₂ =>
      ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩)
      (c' := Code.eraseOff (.block (saltFits zH))) rfl (by taint_decide)))
    fun a u ⟨⟨s, h, j, hem, x9, x10⟩, hb⟩ => ?_) ?_)
  · rw [eval_nonzero, x10, Option.some.injEq, decide_eq_false_iff_not] at hb
    have hk2 := h.1.k2
    refine WP.seq (WP.mono_syms (expLen_ok (lay_of h.1 j.e.sp j.e.x20 j.e.wr) j.e.fr.any j.e.fr.sl)
      fun u₁ ⟨O₁, x12₁⟩ sy₁ => ?_)
    exact WP.mono_syms (saltFitsR_ok T.H hD (a := (s.gpr .x2).toNat) (by omega) (by omega)
      (by rw [O₁.get .x9, x9]) x12₁)
      fun w ⟨O₂, x9₂, x10₂⟩ sy₂ => ⟨s, h, (j.only O₁ sy₁).only O₂ sy₂,
        fun i hi => by rw [O₂.mem, O₁.mem]; exact hem i hi, x9₂, x10₂, hb⟩
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by
      rw [eval_nonzero, eval_nonzero, j₁.x10, j₂.x10, h₁.gpr (r := .x2) (by decide), h₂.gpr (r := .x2) (by decide),
        h₁.gpr (r := .x4) (by decide), h₂.gpr (r := .x4) (by decide), h₁.any, h₂.any])
    (ret0_ct fun a u ⟨⟨s, h, j⟩, _⟩ => by rw [j.c.e.sp, h.fb]) (main_ct hH hGm hGh hGl hGv hc hdo)

end

end VG.Proof.RsaPss.AArch64.Chk
