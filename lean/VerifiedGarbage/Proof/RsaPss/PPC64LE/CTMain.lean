module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTPost
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTPub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.ByIdx
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfStepsT

/-!
# RSASSA-PSS verification on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data and tables (`PreT`, `PubT`), whose hash
function's table holds the same index, leak alike (`code_ct`): the load of
the index and the choice by it (`byIdx_ct`), the checks'
blocks by the taint analysis and their branches by `two_ite`, on values both
runs compute from the public data (the modulus' first byte, its length and
the salt-length mode and length); the call of
`vg_rsa_public_precomputed_checked` by its contract (`pdCallCT`); and the
rest by `post_ct`, from the states `BL` after the call.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (frameBytes restore oRsa arg tword)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.PPC64LE (compressK)
open VG.Proof.MdHashTable.PPC64LE (digestK)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits off fx kR Agree Ok B pins_of two_seq HashCT words_entry bytes_entry
  allocated_sp allocated_gpr restore_taint Saves fb SC TabS)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_ite two_alloc eval_zero eval_nonzero pdCallCT)
open VG.Proof.Mgf1 (ifp ifn)

/-- An entry state, with the tables. -/
abbrev PreT (Z : Tabs) (D : Nat) (s : State) : Prop := PreP D s ∧ TabsOn Z s

/-- The anchor's public data and tables. -/
abbrev PubT (Z : Tabs) (a s : State) : Prop := PubK a s ∧ TabsAg Z a s

section
variable {D : Nat} {Z : Tabs}

theorem tOk : Ok Sp (vP D) (PreT Z D) (PubT Z) := ⟨fun P => P.1.fits, fun p => p.1.1.agree p.1.2⟩

/-- An entry state with the anchor's public data, and `Base` from it. -/
theorem pk_pins {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → ∃ s, PreT Z D s ∧ PubT Z (an x) s ∧ Base Sp (vP D) s t) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs :=
  pins_of tOk h rs hrs

theorem call_ct : RelCT isa (Two fun a t => ∃ s, PreT Z D s ∧ PubT Z a s ∧ AtCall D s t)
    Impl.RsaPkcs1Sig.PPC64LE.pubCall fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, P₁, p₁, c₁⟩, ⟨s₂, P₂, p₂, c₂⟩⟩ => ⟨pdOk_of P₁.1 c₁, pdOk_of P₂.1 c₂,
    ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.base.sp, c₂.base.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g3, c₂.g3, p₁.1.1.pSp, p₂.1.1.pSp]
    · rw [c₁.g4, c₂.g4, p₁.1.1.g _ (by decide), p₂.1.1.g _ (by decide)]
    · rw [c₁.g5, c₂.g5, p₁.1.1.args 4 (by decide) (by decide), p₂.1.1.args 4 (by decide) (by decide)]
    · rw [c₁.g6, c₂.g6, p₁.1.1.args 5 (by decide) (by decide), p₂.1.1.args 5 (by decide) (by decide)]
    · rw [c₁.g7, c₂.g7, p₁.1.1.g _ (by decide), p₂.1.1.g _ (by decide)]
    · rw [c₁.g8, c₂.g8, p₁.1.1.g _ (by decide), p₂.1.1.g _ (by decide)]
    · rw [c₁.g9, c₂.g9, p₁.1.1.g _ (by decide), p₂.1.1.g _ (by decide)]
    · rw [c₁.g10, c₂.g10, p₁.1.1.g _ (by decide), p₂.1.1.g _ (by decide)]
  · rw [c₁.a0, c₂.a0, p₁.1.1.pSp, p₂.1.1.pSp]
  · rw [c₁.a1, c₂.a1, p₁.1.1.args 3 (by decide) (by decide), p₂.1.1.args 3 (by decide) (by decide)]
  · rw [c₁.g5, c₂.g5, c₁.g6, c₂.g6, words_entry c₁.base.mem P₁.1.kp ((P₁.1.sp).sub_left (sc_sub P₁.1)) P₁.1.wp,
      words_entry c₂.base.mem P₂.1.kp ((P₂.1.sp).sub_left (sc_sub P₂.1)) P₂.1.wp, p₁.1.1.w, p₂.1.1.w]
  · rw [c₁.g7, c₂.g7, c₁.g8, c₂.g8,
      bytes_entry c₁.base.mem P₁.1.ke ((P₁.1.es.symm).sub_left (sc_sub P₁.1)) (by have := P₁.1.we; omega_arith),
      bytes_entry c₂.base.mem P₂.1.ke ((P₂.1.es.symm).sub_left (sc_sub P₂.1)) (by have := P₂.1.we; omega_arith),
      p₁.1.1.e, p₂.1.1.e]

end

/-- The checks passed, for an entry state. -/
structure Ck (D : Nat) (s : State) : Prop where
  h0 : s.mem (s.gpr .r3) ≠ 0
  em : D + 2 ≤ kk s - loN s
  fit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - D - 1

section
variable {Z : Tabs} {Gs Gm : Spec.Mgf1.Hash} (hH : HashOK Z.H) (cH : HashCT hH)
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = Z.H.D) (hHv : Proof.Mgf1.Valid Gs)
  (hG : HashOK Z.G) (cG : HashCT hG) (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = Z.G.D)
  (hGmv : Proof.Mgf1.Valid Gm) {P' : Params} {md : Md P'.B P'.N P'.L} (ok : CtOK P' md Z.cc Z.dc)
  (ct : CtTaint P') (hcc : ConstantTime isa (compressK md).pre (compressK md).pub Z.cc)
  (hdc : ConstantTime isa (digestK md).pre (digestK md).pub Z.dc) {iv : md.HV} (hl : md.Link hH.SH iv Gs.len)
  (hN : Z.H.N = P'.N) (hB : Z.H.B = P'.B)

include hH hGl in
/-- After the call, from an entry state that passed the checks. -/
theorem bl_after {a s t : State} (P : PreT Z Gs.len s) (p : PubT Z a s) (c : AfterCall Gs.len s t)
    (sy : t.syms = s.syms) (C : Ck Gs.len s) : BL Gs.len Z a t ∧ Fit Gs.len a := by
  have L := lay_reE P.1 hH hGl c.mem C.h0 C.em
  have g := p.1.1.agree (D := Gs.len) p.1.2
  have hS := reE_Sp P.1 c.mem
  have hSC : SC Sp (reE s t.mem) = SC Sp s := by simp only [SC, hS]
  have hA : ∀ j < 8, ∀ r ∈ [kR s, scR s], Region.Disjoint ⟨stackArgAddr s j, 8⟩ r := fun j hj r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.1.ka.sub_right (in_aR_sub hj)).symm
    · exact (P.1.sa.sub_right (in_aR_sub hj)).symm
  have Tg' : TabS Z.G Z.g gArg Sp (reE s t.mem) (stackArg s 7) := P.2.1.transfer rfl rfl rfl hSC c.mem (hA 7 (by decide)) fun k hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.1.ktg.sub_right (tab_sub (n := 5) hk)).symm
    · exact (P.1.stg.sub_right (tab_sub (n := 5) hk)).symm
  have T' : MdTabS Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Sp (reE s t.mem) (stackArg s 6) := P.2.2.transfer rfl rfl rfl hSC c.mem (hA 6 (by decide)) fun k hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.1.kth.sub_right (tab_sub (n := 11) hk)).symm
    · exact (P.1.sth.sub_right (tab_sub (n := 11) hk)).symm
  have e6 := reE_args P.1 c.mem 6 (by decide)
  have e7 := reE_args P.1 c.mem 7 (by decide)
  have g' : Agree Sp (vP Gs.len) a (reE s t.mem) :=
    ⟨(reE_sp _ _).trans p.1.1.sp, hS.trans p.1.1.pSp, fun r hr => by rw [reE_vP P.1 c.mem]; exact g.v r hr⟩
  have q := p.2
  refine ⟨⟨reE s t.mem, ⟨L.canon, by rw [TabsOn, e6, e7]; exact ⟨Tg', T'⟩⟩,
    ⟨g', by rw [e7]; exact q.1, q.2.1, q.2.2.1, q.2.2.2.1, by rw [e6]; exact q.2.2.2.2.1, q.2.2.2.2.2⟩, c.base, sy⟩,
    fun ha => ?_⟩
  have hk2 : kk s ≤ 1024 := P.1.k2
  have e21 : dbLen Gs.len s = dbLen Gs.len a := g.v .r21 (by decide)
  have hdb : (dbLen Gs.len (reE s t.mem)).toNat = kk s - loN s - Gs.len - 1 := by
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have e : dbLen Gs.len (reE s t.mem) = dbLen Gs.len s := by
    unfold dbLen; rw [lo_reE P.1 c.mem]; rfl
  rw [← e21, ← e, hdb, ← p.1.1.args 0 (by decide) (by decide)]
  exact C.fit (by rw [p.1.1.pAny]; exact ha)

include hH cH hGl hG cG hGmh hGml hGmv ok ct hcc hdc in
theorem main_ct : RelCT isa (Two fun a t => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Before Gs.len s t ∧
      t.syms = s.syms ∧ Ck Gs.len s) (verifyMain Z.H P' Z.f Z.g) fun _ _ => True := by
  refine two_seq (Ψ := fun a t => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ AtCall Gs.len s t ∧ t.syms = s.syms ∧
      Ck Gs.len s)
    (pubArgs_taint (pk_pins (fun _ _ ⟨s, P, p, B, _⟩ => ⟨s, P, p, B.base⟩) []))
    (fun a t ⟨s, P, p, B, sy, C⟩ => WP.mono_syms (pubArgs_ok P.1 B) fun t' c y => ⟨s, P, p, c, y.trans sy, C⟩) ?_
  refine two_seq (Ψ := fun a t => BL Gs.len Z a t ∧ Fit Gs.len a)
    (call_ct.mono (fun _ _ ⟨a, ⟨s₁, P₁, p₁, c₁, _⟩, ⟨s₂, P₂, p₂, c₂, _⟩⟩ =>
      ⟨a, ⟨s₁, P₁, p₁, c₁⟩, ⟨s₂, P₂, p₂, c₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, p, c, sy, C⟩ => WP.mono_syms (call_ok P.1 c) fun t' c' y =>
      bl_after hH hGl P p c' (y.trans sy) C) ?_
  exact post_ct hH cH hGl.symm hG cG hGmh hGml hGmv ok ct hcc hdc

/-- After the entry, from an entry state with the anchor's public data. -/
abbrev En (Z : Tabs) (D : Nat) (a t : State) : Prop :=
  ∃ s, PreT Z D s ∧ PubT Z a s ∧ Entered D s t ∧ t.syms = s.syms

include hH cH hGl hG cG hGmh hGml hGmv ok ct hcc hdc in
theorem checks_ct : RelCT isa (Two (En Z Gs.len)) (checks Z.H P' Z.f Z.g) fun _ _ => True := by
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → En Z Gs.len a t) → Pins Φ [] := fun h =>
    pk_pins (an := id) (fun a t hp => let ⟨s, P, p, E, _⟩ := h a t hp; ⟨s, P, p, E.base⟩) []
  -- The modulus' first byte.
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => by
      rw [eval_zero, eval_zero, E₁.r9, E₂.r9, p₁.1.1.pN0 p₁.1.2, p₂.1.1.pN0 p₂.1.2])
    (fail_taint (pin fun _ _ h => h.1)) ?_
  let E1 := fun (a t : State) => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Entered Gs.len s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .r3) ≠ 0
  -- `emLen < hLen + 2`.
  refine two_seq (Ψ := fun a t => E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < Gs.len + 2))
    (chkEm_taint Z.H (pin fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, E, sy⟩, hz⟩ => ?_) ?_
  · have h0 := n0_ne E (by rw [eval_zero] at hz; exact Option.some.inj hz)
    exact WP.mono_syms (chkEm_ok P.1 hGl hD64 E h0) fun t' ⟨E', r3⟩ y =>
      ⟨⟨s, P, p, E', y.trans sy, h0⟩, by rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin fun _ _ h => let ⟨s, P, p, E, sy, _⟩ := h.1.1; ⟨s, P, p, E, sy⟩)) ?_
  let E2 := fun (a t : State) => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Entered Gs.len s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .r3) ≠ 0 ∧ Gs.len + 2 ≤ kk s - loN s
  have e2 : ∀ {a t : State}, (E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < Gs.len + 2)) ∧
      isa.eval (.nonzero .d .r3) t = some false → E2 a t := fun {a t} ⟨⟨⟨s, P, p, E, sy, h0⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have : ¬ kk a - loN a < Gs.len + 2 := by simpa using hc
    exact ⟨s, P, p, E, sy, h0, by rw [p.1.1.pKk, p.1.1.pLoN p.1.2]; omega_arith⟩
  -- The salt length expected.
  let E3 := fun (a t : State) => E2 a t ∧ t.gpr .r4 = if anyL a = 0 then stackArg a 0 else 0
  refine two_seq (Ψ := E3) (expLen_taint (pk_pins (an := id) (fun a t hp =>
      let ⟨s, P, p, E, _⟩ := e2 hp; ⟨s, P, p, E.base⟩) [.r20]))
    (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, E, sy, h0, hem⟩ := e2 h
    exact WP.mono_syms (expLen_ok E.base.pany E.base.psl) fun t' ⟨o, e⟩ y =>
      ⟨⟨s, P, p, E.only P.1 o, y.trans sy, h0, hem⟩, by
        rw [e, p.1.1.pAny, p.1.1.args 0 (by decide) (by decide)]⟩
  refine two_seq (Ψ := fun a t => E2 a t ∧ (t.gpr .r3 != 0) =
      decide (kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then stackArg a 0 else 0).toNat))
    (chkSalt_taint Z.H (pin fun _ _ h => let ⟨s, P, p, E, sy, _⟩ := h.1; ⟨s, P, p, E, sy⟩))
    (fun a t ⟨⟨s, P, p, E, sy, h0, hem⟩, h4⟩ => WP.mono_syms (chkSalt_ok P.1 hGl hD64 E h0 hem
      (by rw [h4, p.1.1.pAny, p.1.1.args 0 (by decide) (by decide)])) fun t' ⟨E', r3⟩ y =>
        ⟨⟨s, P, p, E', y.trans sy, h0, hem⟩, by
          rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2, p.1.1.pAny, p.1.1.args 0 (by decide) (by decide)]⟩) ?_
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin fun _ _ h => let ⟨s, P, p, E, sy, _⟩ := h.1.1; ⟨s, P, p, E, sy⟩)) ?_
  have e4 : ∀ {a t : State}, (E2 a t ∧ (t.gpr .r3 != 0) =
      decide (kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then stackArg a 0 else 0).toNat)) ∧
      isa.eval (.nonzero .d .r3) t = some false →
      ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Before Gs.len s t ∧ t.syms = s.syms ∧ Ck Gs.len s :=
    fun {a t} ⟨⟨⟨s, P, p, E, sy, h0, hem⟩, c⟩, hc⟩ => by
      rw [eval_nonzero, c] at hc
      have hn : ¬ kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then stackArg a 0 else 0).toNat := by simpa using hc
      refine ⟨s, P, p, E.before, sy, h0, hem, fun ha => ?_⟩
      rw [← p.1.1.pAny, ifp ha, ← p.1.1.args 0 (by decide) (by decide), ← p.1.1.pKk, ← p.1.1.pLoN p.1.2] at hn
      omega_arith
  exact (main_ct hH cH hGl hG cG hGmh hGml hGmv ok ct hcc hdc).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, e4 h₁, e4 h₂⟩) fun _ _ h => h

/-- After the frame's push and the choice by the index, from an entry state. -/
abbrev Ix (Z : Tabs) (D i : Nat) (a u : State) : Prop :=
  ∃ s, (PreT Z D s ∧ PubT Z a s) ∧ Only [.r11, .r12] (allocated frameBytes s) u ∧ u.syms = s.syms ∧
    u.gpr .r11 = BitVec.ofNat 64 i

include hH cH hGh hGl hHv hG cG hGmh hGml hGmv ok ct hcc hdc hl hN hB in
/-- The frame's body, for the hash function's sizes. -/
theorem body_ct {i : Nat} : RelCT isa (Two (Ix Z Gs.len i)) (body Z.H P' Z.f Z.g) fun _ _ => True := by
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  refine two_seq (Ψ := En Z Gs.len)
    (entry_taint Z.H fun a u₁ u₂ ⟨s₁, h₁, o₁, _⟩ ⟨s₂, h₂, o₂, _⟩ => ⟨by rw [o₁.sp, o₂.sp, allocated_sp,
      allocated_sp, h₁.2.1.1.sp, h₂.2.1.1.sp], fun r hr => by
        rw [List.mem_singleton.mp hr, o₁.get .r3, o₂.get .r3, allocated_gpr, allocated_gpr, h₁.2.1.1.g .r3 (by decide),
          h₂.2.1.1.g .r3 (by decide)]⟩)
    (fun a u ⟨s, ⟨P, p⟩, o, sy, _⟩ => WP.mono_syms (entry_ok P.1 hGl.symm hD64 o) fun t E y =>
      ⟨s, P, p, E, y.trans sy⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Saves s t)
    (checks_ct hH cH hGl hG cG hGmh hGml hGmv ok ct hcc hdc) fun a t ⟨s, P, p, E, sy⟩ =>
      WP.mono (checks_done P.1 hH hGh hGl hHv hG P.2.1 hGmh hGml hGmv P.2.2 ok hl hN hB E sy) fun t' d =>
        ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp], fun _ h => nomatch h⟩

include hH cH hGh hGl hHv hG cG hGmh hGml hGmv ok ct hcc hdc hl hN hB in
/-- Two runs of `vg_rsa_pss_verify_precomputed` from entry states with the
same public data and tables, whose hash function's table holds the index
`i` of `H`'s sizes, leak alike. -/
theorem code_ct {i : Nat} (hi : i ∈ idxs) (hD : (shapeOf i).1.D = Z.H.D) (hP : (shapeOf i).2 = P') :
    RelCT isa (Two fun a s => (PreT Z Gs.len s ∧ PubT Z a s) ∧
      s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i)
      (verifyPrecomputed Z.f Z.g) fun _ _ => True := by
  have hi8 : i < 8 := by simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.1.2.1.1.sp.trans h₂.1.2.1.1.sp.symm, fun _ h => nomatch h⟩) ?_
  let A0 := fun (a s : State) => (PreT Z Gs.len s ∧ PubT Z a s) ∧
    s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i
  let A1 := fun (a u : State) => ∃ s, A0 a s ∧ Only [.r11] (allocated frameBytes s) u ∧ u.syms = s.syms ∧
    u.gpr .r11 = stackArg s 6
  let A2 := fun (a u : State) => ∃ s, A0 a s ∧ Only [.r11] (allocated frameBytes s) u ∧ u.syms = s.syms ∧
    u.gpr .r11 = BitVec.ofNat 64 i
  have spA : ∀ {a s₁ s₂ : State}, A0 a s₁ → A0 a s₂ → (allocated frameBytes s₁).sp = (allocated frameBytes s₂).sp :=
    fun h₁ h₂ => by rw [allocated_sp, allocated_sp, h₁.1.2.1.1.sp, h₂.1.2.1.1.sp]
  show RelCT isa _ (.seq (.block ([.addSp .r11 0, .load .d .r11 .r11 (arg hArg)] ++ [.load .d .r11 .r11 (8 * 5)]))
    _) _
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_post (Ψ := A1)
      (twA11_taint hArg fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; exact spA h₁ h₂, fun _ h => nomatch h⟩)
      fun a u ⟨s, h, e⟩ => ?_)
    (two_post (Ψ := A2) (twB11_taint (8 * 5) fun a u₁ u₂ ⟨s₁, h₁, o₁, _, e₁⟩ ⟨s₂, h₂, o₂, _, e₂⟩ =>
      ⟨by rw [o₁.sp, o₂.sp]; exact spA h₁ h₂, fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂, h₁.1.2.1.1.args 6 (by decide) (by decide),
          h₂.1.2.1.1.args 6 (by decide) (by decide)]⟩) fun a u ⟨s, h, o, y, e⟩ => ?_))) ?_
  · subst e
    exact WP.of_syms ((argA_ok (j := hArg) (by decide) ⟨aR s, by rw [h.1.1.1.hrd]; simp, in_aR (by decide)⟩
      (h.1.1.1.ka.sub_right (in_aR_sub (by decide))).symm).mono fun u' ⟨o', e'⟩ y => ⟨s, h, o', y, e'⟩)
  · have P := h.1.1.1
    exact WP.of_syms ((wordA_ok o e (by decide) ⟨tHR s, by rw [P.hrd]; simp, Offset.contains_base _ (by decide)
      (by decide)⟩ (P.kth.sub_right (tab_sub (n := 11) (show 5 < 11 by decide))).symm).mono fun u' ⟨o', e'⟩ y' =>
        ⟨s, h, o', y'.trans y, by rw [e']; exact h.2⟩)
  refine byIdx_ct (D := i) (by omega) (Φ := Ix Z Gs.len i)
    (fun _ _ ⟨_, _, _, _, e⟩ => e) (fun a u₁ u₂ ⟨s₁, h₁, o₁, _⟩ ⟨s₂, h₂, o₂, _⟩ => by
      rw [o₁.sp, o₂.sp, allocated_sp, allocated_sp, h₁.2.1.1.sp, h₂.2.1.1.sp])
    (fun a u u' ⟨s, h, o, y, e⟩ o' y' => ⟨s, h, (o.trans o').mono, y'.trans y, by rw [o'.get .r11]; exact e⟩)
    ?_ hi idxs_certs |>.mono (fun _ _ ⟨a, ⟨s₁, h₁, o₁, y₁, e₁⟩, ⟨s₂, h₂, o₂, y₂, e₂⟩⟩ =>
      ⟨a, ⟨s₁, h₁.1, o₁.mono, y₁, e₁⟩, ⟨s₂, h₂.1, o₂.mono, y₂, e₂⟩⟩) fun _ _ h => h
  · rw [body_D hD, hP]
    exact body_ct hH cH hGh hGl hHv hG cG hGmh hGml hGmv ok ct hcc hdc hl hN hB

end

end VG.Proof.RsaPss.PPC64LE
