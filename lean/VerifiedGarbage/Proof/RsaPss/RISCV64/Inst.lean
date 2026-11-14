module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.CTPost
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Correct
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaPss.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
public import VerifiedGarbage.Proof.MdHashTable.RISCV64.Tables
import VerifiedGarbage.Proof.RsaPss.RISCV64.ByIdx
import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Impl.RsaPss.RISCV64

/-! ### `RsaPss.RISCV64.Verified`, which only this module used -/

section

/-!
# RSASSA-PSS verification on RISC-V: constant time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/CTPub.lean`, `CTMain.lean`): the public data of an
entry state (`PubP`: the pointers, the lengths, the salt-length mode, the
modulus, `e` and `pre`) fixes what `Base` fixes (`pssOk`) and `c`,
`salt_len` and the mode (`PubP.agreeP`); with the tables (`PreT`, `PubT`:
both at the anchor's addresses, with their functions at the anchor's
addresses). Two runs from entry states with the same public data leak alike
(`code_ct`): the checks (`checks_ct`) branch on public values, the call of
the public operation leaks what it leaks for its public arguments
(`call_ct`), and the code after it is `post_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits off fx kR SC Agree Ok B BT TabS pins_of two_seq HashCT words_entry
  bytes_entry restore_taint Saves fb stackBytes)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_ite two_alloc eval_zero eval_nonzero pdCallCT)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s. -/
structure PubP (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], s.gpr r = a.gpr r
  a0 : stackArg s 0 = stackArg a 0
  a1 : (stackArg s 1).setWidth 32 = (stackArg a 1).setWidth 32
  args : ∀ i, 2 ≤ i → i < 8 → stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .a0) (kk s) = Spec.Rsa.bytesAt a.mem (a.gpr .a0) (kk a)
  e : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a2) (a.gpr .a3).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 4) (stackArg a 5).toNat

theorem pubP_refl (s : State) : PubP s s := ⟨rfl, fun _ _ => rfl, rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem leak_eq3 {a b c d : List Byte} {w w' : List (BitVec 64)} (ha : a.length = c.length)
    (hb : b.length = d.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (c ++ d).map (·.toNat) ++ w'.map (·.toNat)) :
    a = c ∧ b = d ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = c ++ d := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  exact ⟨(List.append_inj hi ha).1, (List.append_inj hi ha).2,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

/-- The contract's public data: `PubP`, the tables' functions at the same
addresses, and the same tables held. -/
theorem pubP_of {tsH tsG : List FnTable} {s₁ s₂ : State} (h : (verSpec tsH tsG).pub s₁ s₂) :
    PubP s₁ s₂ ∧
      (∀ f ∈ (tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten,
        s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 6) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 6) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 7) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 7) (FnTable.words isa s₂ T)) := by
  have e : stackBytes = 335 + 1 := rfl
  unfold verSpec at h
  rw [e] at h
  sig_pub [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_eight, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htabH, htabG, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  obtain ⟨hn, he, hw⟩ := leak_eq3 (by simp [bytesAt_length, h1]) (by simp [bytesAt_length, h3]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, a0.symm, a1.symm, fun i h2 hi => ?_, hn.symm, he.symm, hw.symm⟩, hsy,
    fun T hT => htabH _ _ rfl rfl T hT, fun T hT => htabG _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega_using [h2, hi] : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm]

section
variable {a s : State} (p : PubP a s)
include p

theorem PubP.pKk : kk s = kk a := by rw [kk, kk, p.g .a1 (by decide)]

theorem PubP.byte (hk : 1 ≤ kk s) : s.mem (s.gpr .a0) = a.mem (a.gpr .a0) := by
  have e1 : kk s = kk a := p.pKk
  have := congrArg (·.getD 0 0) p.n
  rwa [bytesAt_getD _ _ hk, bytesAt_getD _ _ (by omega), BitVec.add_zero, BitVec.add_zero] at this

theorem PubP.pAny : anyL s = anyL a := by
  have e : ∀ x : BitVec 64, x <<< 32 >>> 32 = (x.setWidth 32).setWidth 64 := fun x => by
    apply BitVec.eq_of_toNat_eq
    have := x.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    omega_using []
  unfold anyL; rw [e, e, p.a1]

theorem PubP.pN0 (hk : 1 ≤ kk s) : n0 s = n0 a := by rw [n0, n0, p.byte hk]

theorem PubP.pLo (hk : 1 ≤ kk s) : lo s = lo a := by simp only [lo, smear, p.pN0 hk]

theorem PubP.pCm (hk : 1 ≤ kk s) : cm s = cm a := by rw [cm, cm, p.pLo hk]; simp only [smear, p.pN0 hk]

theorem PubP.pLoN (hk : 1 ≤ kk s) : loN s = loN a := by rw [loN, loN, p.byte hk]

theorem PubP.pSp : Sp s = Sp a := p.args 2 (by decide) (by decide)

theorem PubP.agree {D : Nat} (hk : 1 ≤ kk s) : Agree Sp (vP D) a s := ⟨p.sp, p.pSp, fun r hr => by
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [vP]
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.pLo hk
  · rw [dbLen, dbLen, p.pLo hk, p.g .a1 (by decide)]⟩

theorem PubP.agreeP {D : Nat} (hk : 1 ≤ kk s) : AgreeP D a s :=
  ⟨p.agree hk, p.pCm hk, p.a0, p.pAny⟩

end

/-- `PubP`, for a nonempty modulus. -/
def PubK (a s : State) : Prop := PubP a s ∧ 1 ≤ kk s

/-- `PubK` gives what the shared code needs. -/
theorem pssOk (D : Nat) : Ok Sp (vP D) (PreP D) PubK where
  fits P := P.fits
  agree p := p.1.agree p.2

/-! ## The call -/

section
variable {D : Nat}

/-- An entry state with the anchor's public data, and `Base` from it. -/
theorem pk_pins {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → ∃ s, PreP D s ∧ PubK (an x) s ∧ Base Sp (vP D) s t) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ Reg.s0 :: fx := by decide) : Pins Φ rs :=
  pins_of (pssOk D) h rs hrs

theorem call_ct : RelCT isa (Two fun a t => ∃ s, PreP D s ∧ PubK a s ∧ AtCall D s t)
    Impl.RsaPkcs1Sig.RISCV64.pubCall fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, P₁, p₁, c₁⟩, ⟨s₂, P₂, p₂, c₂⟩⟩ => ⟨pdOk_of P₁ c₁, pdOk_of P₂ c₂,
    ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.base.sv.sp, c₂.base.sv.sp, fb, fb, p₁.1.sp, p₂.1.sp]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g0, c₂.g0, p₁.1.pSp, p₂.1.pSp]
    · rw [c₁.g1, c₂.g1, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g2, c₂.g2, p₁.1.args 4 (by decide) (by decide), p₂.1.args 4 (by decide) (by decide)]
    · rw [c₁.g3, c₂.g3, p₁.1.args 5 (by decide) (by decide), p₂.1.args 5 (by decide) (by decide)]
    · rw [c₁.g4, c₂.g4, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g5, c₂.g5, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g6, c₂.g6, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g7, c₂.g7, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
  · rw [c₁.a0, c₂.a0, p₁.1.pSp, p₂.1.pSp]
  · rw [c₁.a1, c₂.a1, p₁.1.args 3 (by decide) (by decide), p₂.1.args 3 (by decide) (by decide)]
  · rw [c₁.g2, c₂.g2, c₁.g3, c₂.g3, words_entry c₁.base.mem P₁.kp ((P₁.sp).sub_left (sc_sub P₁)) P₁.wp,
      words_entry c₂.base.mem P₂.kp ((P₂.sp).sub_left (sc_sub P₂)) P₂.wp, p₁.1.w, p₂.1.w]
  · rw [c₁.g4, c₂.g4, c₁.g5, c₂.g5,
      bytes_entry c₁.base.mem P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega_using []),
      bytes_entry c₂.base.mem P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega_using []), p₁.1.e, p₂.1.e]

end

/-! ## The function -/

/-- The precondition, with the tables on entry. -/
def PreT (D : Nat) (W : VT) (s : State) : Prop :=
  PreP D s ∧ TabM W.M W.dg W.f 6 Sp s (stackArg s 6) ∧ TabS W.G W.g 7 Sp s (stackArg s 7)

/-- The public data, with the tables' functions at the anchor's addresses. -/
def PubT (W : VT) (a s : State) : Prop := PubK a s ∧ ∀ n ∈ W.names, s.syms n = a.syms n

/-- The checks passed, for an entry state. -/
structure Ck (D : Nat) (s : State) : Prop where
  h0 : s.mem (s.gpr .a0) ≠ 0
  em : D + 2 ≤ kk s - loN s
  fit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - D - 1

section
variable {W : VT} (cH : HashCT W.hH) (hF : W.H.F ≤ 208) {Hs : Spec.Mgf1.Hash} (hHl : Hs.len = W.H.D)
  (hG : HashOK W.G) (cG : HashCT hG) (hFG : W.G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = W.G.D) (hGv : Proof.Mgf1.Valid Gs)
  (hHh : ∀ x, Hs.hash x = W.hH.SH.H.hash x) (hHv : Proof.Mgf1.Valid Hs)

include hHl in
/-- After the call, from an entry state that passed the checks. -/
theorem bl_after {a s t : State} (P : PreT Hs.len W s) (p : PubT W a s) (c : AfterCall Hs.len s t)
    (sy : t.syms = s.syms) (C : Ck Hs.len s) : BL Hs.len W a t ∧ Xa a t ∧ Fit Hs.len a := by
  have L := lay_reE P.1 W.hH hHl c.mem C.h0 C.em
  have g := p.1.1.agreeP (D := Hs.len) p.1.2
  have hany : anyL (reE s t.mem) = anyL s := by unfold anyL; rw [reE_args P.1 c.mem 1 (by decide)]
  have g' : AgreeP Hs.len a (reE s t.mem) :=
    ⟨⟨(reE_sp _ _).trans p.1.1.sp, (reE_Sp P.1 c.mem).trans p.1.1.pSp, fun r hr => by
      rw [reE_vP P.1 c.mem]; exact g.ag.v r hr⟩, (cm_reE P.1 c.mem).trans g.cm,
      (reE_args P.1 c.mem 0 (by decide)).trans g.sl, hany.trans g.any⟩
  have hS := reE_Sp P.1 c.mem
  have hSC : SC Sp (reE s t.mem) = SC Sp s := by simp only [SC, hS]
  have e6 := reE_args P.1 c.mem 6 (by decide)
  have e7 := reE_args P.1 c.mem 7 (by decide)
  have T' : TabM W.M W.dg W.f 6 Sp (reE s t.mem) (stackArg (reE s t.mem) 6) := by
    rw [e6]; exact P.2.1.transfer rfl rfl rfl hSC c.mem (arg_dis P.1 (by decide)) (tabH_dis P.1)
  have TG' : TabS W.G W.g 7 Sp (reE s t.mem) (stackArg (reE s t.mem) 7) := by
    rw [e7]; exact P.2.2.transfer rfl rfl rfl hSC c.mem (arg_dis P.1 (by decide)) (tabG_dis P.1)
  refine ⟨⟨reE s t.mem, ⟨L.canon, T', TG'⟩, ⟨g', by rw [e6, p.1.1.args 6 (by decide) (by decide)],
    by rw [e7, p.1.1.args 7 (by decide) (by decide)], p.2⟩, c.base, sy⟩, c.xs.xa g', fun ha => ?_⟩
  have hk2 : kk s ≤ 1024 := P.1.k2
  have e4 : dbLen Hs.len s = dbLen Hs.len a := g.ag.v .s4 (by decide)
  have hdb : (dbLen Hs.len (reE s t.mem)).toNat = kk s - loN s - Hs.len - 1 := by
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk2])]
  have e : dbLen Hs.len (reE s t.mem) = dbLen Hs.len s := by
    unfold dbLen; rw [reE_lo P.1 c.mem]; rfl
  rw [← e4, ← e, hdb, ← p.1.1.a0]
  exact C.fit (by rw [p.1.1.pAny]; exact ha)

include cH hF hHl hG cG hFG hGh hGl hGv in
theorem main_ct : RelCT isa (Two fun a t => ∃ s, PreT Hs.len W s ∧ PubT W a s ∧ Before Hs.len s t ∧
    t.syms = s.syms ∧ Ck Hs.len s) (verifyMain W.H W.M.be W.f W.g) fun _ _ => True := by
  refine two_seq (Ψ := fun a t => ∃ s, PreT Hs.len W s ∧ PubT W a s ∧ AtCall Hs.len s t ∧ t.syms = s.syms ∧
      Ck Hs.len s)
    (pubArgs_taint (pk_pins (fun _ _ ⟨s, P, p, B, _⟩ => ⟨s, P.1, p.1, B.base⟩) []))
    (fun a t ⟨s, P, p, B, y, C⟩ => WP.mono_syms (pubArgs_ok P.1 B) fun t' c y' => ⟨s, P, p, c, y'.trans y, C⟩) ?_
  refine two_seq (Ψ := fun a t => BL Hs.len W a t ∧ Xa a t ∧ Fit Hs.len a)
    (call_ct.mono (fun _ _ ⟨a, ⟨s₁, P₁, p₁, c₁, _⟩, ⟨s₂, P₂, p₂, c₂, _⟩⟩ =>
      ⟨a, ⟨s₁, P₁.1, p₁.1, c₁⟩, ⟨s₂, P₂.1, p₂.1, c₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, p, c, y, C⟩ => WP.mono_syms (call_ok P.1 c) fun t' c' y' =>
      bl_after hHl P p c' (y'.trans y) C) ?_
  exact post_ct cH hF hHl.symm hG cG hFG hGh hGl hGv

/-- After the entry, from an entry state with the anchor's public data. -/
abbrev En (D : Nat) (W : VT) (a t : State) : Prop :=
  ∃ s, PreT D W s ∧ PubT W a s ∧ Entered D s t ∧ t.syms = s.syms

include cH hF hHl hG cG hFG hGh hGl hGv in
theorem checks_ct : RelCT isa (Two (En Hs.len W)) (checks W.H W.M.be W.f W.g) fun _ _ => True := by
  have hD64 : Hs.len ≤ 64 := hHl ▸ W.hH.hD64
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → En Hs.len W a t) → Pins Φ [] := fun h =>
    pk_pins (an := id) (fun a t hp => let ⟨s, P, p, E, _⟩ := h a t hp; ⟨s, P.1, p.1, E.base⟩) []
  -- The modulus' first byte.
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => by
      rw [eval_zero, eval_zero, E₁.t1, E₂.t1, p₁.1.1.pN0 p₁.1.2, p₂.1.1.pN0 p₂.1.2])
    (fail_taint (pin fun _ _ h => h.1)) ?_
  let E1 := fun (a t : State) => ∃ s, PreT Hs.len W s ∧ PubT W a s ∧ Entered Hs.len s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .a0) ≠ 0
  have pin1 : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → E1 a t) → Pins Φ [] := fun h =>
    pin fun a t hp => let ⟨s, P, p, E, y, _⟩ := h a t hp; ⟨s, P, p, E, y⟩
  -- `emLen < hLen + 2`.
  refine two_seq (Ψ := fun a t => E1 a t ∧ (t.gpr .a0 != 0) = decide (kk a - loN a < Hs.len + 2))
    (chkEm_taint W.H (pin fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, E, y⟩, hz⟩ => ?_) ?_
  · have h0 := n0_ne E (by rw [eval_zero] at hz; exact Option.some.inj hz)
    exact WP.mono_syms (chkEm_ok P.1 hHl hD64 E h0) fun t' ⟨E', r3⟩ y' =>
      ⟨⟨s, P, p, E', y'.trans y, h0⟩, by rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin1 fun _ _ h => h.1.1)) ?_
  let E2 := fun (a t : State) => ∃ s, PreT Hs.len W s ∧ PubT W a s ∧ Entered Hs.len s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .a0) ≠ 0 ∧ Hs.len + 2 ≤ kk s - loN s
  have pin2 : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → E2 a t) → Pins Φ [] := fun h =>
    pin fun a t hp => let ⟨s, P, p, E, y, _⟩ := h a t hp; ⟨s, P, p, E, y⟩
  have e2 : ∀ {a t : State}, (E1 a t ∧ (t.gpr .a0 != 0) = decide (kk a - loN a < Hs.len + 2)) ∧
      isa.eval (.nonzero .a0) t = some false → E2 a t := fun {a t} ⟨⟨⟨s, P, p, E, y, h0⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have : ¬ kk a - loN a < Hs.len + 2 := by simpa using hc
    exact ⟨s, P, p, E, y, h0, by rw [p.1.1.pKk, p.1.1.pLoN p.1.2]; omega_using [this]⟩
  -- The salt length expected.
  let E3 := fun (a t : State) => E2 a t ∧ t.gpr .a1 = if anyL a = 0 then stackArg a 0 else 0
  have pin7 : Pins (fun (a t : State) => (E1 a t ∧ (t.gpr .a0 != 0) = decide (kk a - loN a < Hs.len + 2)) ∧
      isa.eval (.nonzero .a0) t = some false) [.s7] := fun a t₁ t₂ h₁ h₂ => by
    obtain ⟨s₁, P₁, p₁, E₁, -⟩ := e2 h₁
    obtain ⟨s₂, P₂, p₂, E₂, -⟩ := e2 h₂
    refine ⟨by rw [E₁.base.sv.sp, E₂.base.sv.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp], fun r hr => ?_⟩
    rw [List.mem_singleton.mp hr, E₁.xs.s7, E₂.xs.s7, p₁.1.1.pAny, p₂.1.1.pAny]
  refine two_seq (Ψ := E3) (expLen_taint pin7) (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, E, y, h0, hem⟩ := e2 h
    exact WP.mono_syms (expLen_ok E.xs) fun t' ⟨o, e⟩ y' =>
      ⟨⟨s, P, p, E.only P.1 o, y'.trans y, h0, hem⟩, by rw [e, p.1.1.pAny, p.1.1.a0]⟩
  refine two_seq (Ψ := fun a t => E2 a t ∧ (t.gpr .a0 != 0) =
      decide (kk a - loN a - (Hs.len + 2) < (if anyL a = 0 then stackArg a 0 else 0).toNat))
    (chkSalt_taint W.H (pin2 fun _ _ h => h.1))
    (fun a t ⟨⟨s, P, p, E, y, h0, hem⟩, h1⟩ => WP.mono_syms (chkSalt_ok P.1 hHl hD64 E h0 hem
      (by rw [h1, p.1.1.pAny, p.1.1.a0])) fun t' ⟨E', r3⟩ y' =>
        ⟨⟨s, P, p, E', y'.trans y, h0, hem⟩, by rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2, p.1.1.pAny, p.1.1.a0]⟩) ?_
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin2 fun _ _ h => h.1.1)) ?_
  have e4 : ∀ {a t : State}, (E2 a t ∧ (t.gpr .a0 != 0) =
      decide (kk a - loN a - (Hs.len + 2) < (if anyL a = 0 then stackArg a 0 else 0).toNat)) ∧
      isa.eval (.nonzero .a0) t = some false →
      ∃ s, PreT Hs.len W s ∧ PubT W a s ∧ Before Hs.len s t ∧ t.syms = s.syms ∧ Ck Hs.len s :=
    fun {a t} ⟨⟨⟨s, P, p, E, y, h0, hem⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have hn : ¬ kk a - loN a - (Hs.len + 2) < (if anyL a = 0 then stackArg a 0 else 0).toNat := by simpa using hc
    refine ⟨s, P, p, E.before, y, h0, hem, fun ha => ?_⟩
    rw [← p.1.1.pAny, ifp ha, ← p.1.1.a0, ← p.1.1.pKk, ← p.1.1.pLoN p.1.2] at hn
    omega_using [hem, hn]
  exact (main_ct cH hF hHl hG cG hFG hGh hGl hGv).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, e4 h₁, e4 h₂⟩)
    fun _ _ h => h

include cH hF hHl hG cG hFG hGh hGl hGv hHh hHv in
/-- Two runs of the code for the hash function `W.H` from entry states with
the same public data leak alike. -/
theorem code_ct : RelCT isa (Two fun a s => PreT Hs.len W s ∧ PubT W a s) (verifyFor W.H W.M.be W.f W.g)
    fun _ _ => True := by
  have hD64 : Hs.len ≤ 64 := hHl ▸ W.hH.hD64
  refine two_alloc (R := fun _ _ => True) ?_
  refine two_seq (Ψ := En Hs.len W)
    (entry_taint W.H fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocd, h₁.2.1.1.sp,
      h₂.2.1.1.sp], fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂]
        show (allocd _ s₁).gpr .a0 = (allocd _ s₂).gpr .a0
        simp only [allocd]
        exact (h₁.2.1.1.g .a0 (by decide)).trans (h₂.2.1.1.g .a0 (by decide)).symm⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by
      subst e; exact WP.mono_syms (entry_ok P.1 hHl.symm hD64) fun t E y => ⟨s, P, p, E, y.trans rfl⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreT Hs.len W s ∧ PubT W a s ∧ Saves s t)
    (checks_ct cH hF hHl hG cG hFG hGh hGl hGv) fun a t ⟨s, P, p, E, y⟩ =>
      WP.mono (checks_done P.1 W.hH hF P.2.1 hHh hHl hHv hG hFG P.2.2 hGh hGl hGv E y)
        fun t' d => ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaPss.RISCV64

end

end


/-!
# RSASSA-PSS verification on RISC-V with the tables of `vs` and `gs`

Untrusted: everything here is checked by Lean. `verifyPrecomputed` loads the
index of the hash function of the table `hash` (`idxLoad`, its word 5) and
runs the code for its shape (`byIdx`, `Proof/RsaPss/RISCV64/ByIdx.lean`),
which is the code for the hash function itself when the hash function's
shape is the index's (`Shape`, `verifyFor_shape`). The load changes only
`t5`, and the comparisons `t4`, which nothing the contract states depends
on (`Sim`): so the correctness (`code_ok`) and the constant time
(`code_ct`) of the code for a hash function from the entry state are its
correctness and constant time after the load (`code_correct`,
`code_constantTime`), for the tables of `vs` and `gs` (`Coh`, `OK`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits off kR SC TabS stackBytes stackArgAddr_eq)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_taint wp_ld wp_addSp wp_nil)
open VG.Proof.MdHashTable.RISCV64 (MVar idx digName tableOf tables fnsOf names Coh held_tableOf hashAt_tableOf
  tabM_of)

/-! ## States but for `t4` and `t5` -/

/-- `u` is `s` but for `t4` and `t5`. -/
abbrev Sim (s u : State) : Prop := Only [.t4, .t5] s u ∧ u.syms = s.syms

section
variable {s u : State} (h : Sim s u)
include h

theorem Sim.g {r : Reg} (hr : r ∉ [Reg.t4, .t5] := by decide) : u.gpr r = s.gpr r := h.1.gpr r hr

theorem Sim.addr (i : Nat) : stackArgAddr u i = stackArgAddr s i := by simp only [stackArgAddr, h.1.sp]

theorem Sim.arg (i : Nat) : stackArg u i = stackArg s i := by simp only [stackArg, h.addr, h.1.mem]

theorem Sim.kRe : kR u = kR s := by simp only [Proof.RsaOaep.RISCV64.kR, h.1.sp]

theorem Sim.preP {D : Nat} (P : PreP D s) : PreP D u := by
  have e0 := h.g (r := .a0); have e1 := h.g (r := .a1); have e2 := h.g (r := .a2); have e3 := h.g (r := .a3)
  have e4 := h.g (r := .a4); have e6 := h.g (r := .a6); have e7 := h.g (r := .a7)
  have ea := h.arg; have eA := h.addr; have ek := h.kRe
  have esp := h.1.sp; have erd := h.1.rd; have ewr := h.1.wr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp only [nR, eR, dR, gR, scR, pR, tHR, tGR, aR, e0, e1, e2, e3, e4, e6, e7, ea, eA, ek,
    esp, erd, ewr])
  exacts [P.spal, P.sp1, P.sp2, P.hrd, P.hwr, P.ns, P.es, P.ds, P.gs, P.sp, P.sth, P.stg, P.sa, P.kn, P.ke, P.kd,
    P.kg, P.ksc, P.kp, P.kth, P.ktg, P.ka, P.wn, P.we, P.wd, P.wg, P.wsc, P.wp, P.wth, P.wtg, P.k1, P.k2, P.e1,
    P.e2, P.gk, P.hs, P.hp, P.al2, P.al4, P.al6, P.al7]

theorem Sim.post {Hs Gs : Spec.Mgf1.Hash} {s' : State} (q : Post Hs Gs u s') : Post Hs Gs s s' := by
  have e0 := h.g (r := .a0); have e1 := h.g (r := .a1); have e2 := h.g (r := .a2); have e3 := h.g (r := .a3)
  have e4 := h.g (r := .a4); have e6 := h.g (r := .a6)
  have ea := h.arg; have em := h.1.mem
  have hp : PreOk u = PreOk s := by simp only [PreOk, kk, e0, e1, ea, em]
  have hv : vOut Hs Gs u = vOut Hs Gs s := by simp only [vOut, kk, mh, e0, e1, e2, e3, e4, e6, ea, em]
  obtain ⟨⟨g, sp, ra⟩, r⟩ := q
  exact ⟨⟨fun x hx => (g x hx).trans (h.1.gpr x (by revert x; decide)), sp.trans h.1.sp,
    ra.trans (h.g (r := .ra))⟩, fun c => by rw [← hv]; exact r (by rw [hp]; exact c)⟩

theorem Sim.pubP {a : State} (p : PubP a s) : PubP a u := by
  have e0 := h.g (r := .a0); have e1 := h.g (r := .a1); have e2 := h.g (r := .a2); have e3 := h.g (r := .a3)
  have ea := h.arg; have em := h.1.mem
  exact ⟨h.1.sp.trans p.sp, fun r hr => (h.1.gpr r (by revert r; decide)).trans (p.g r hr),
    (ea 0).trans p.a0, by rw [ea]; exact p.a1, fun i h1 h2 => (ea i).trans (p.args i h1 h2),
    by simp only [kk, e0, e1, em]; exact p.n, by simp only [e2, e3, em]; exact p.e, by simp only [ea, em]; exact p.w⟩

theorem Sim.tabM {H : Hash} {hH : HashOK H} {M : MdL H hH} {dN : String} {f : MdFns} {j : Nat}
    (T : TabM M dN f j Sp s (stackArg s j)) : TabM M dN f j Sp u (stackArg u j) := by
  rw [h.arg]
  exact T.transfer h.1.sp h.1.rd h.2 (by simp only [SC, Sp, h.arg]) (rs := []) (by rw [h.1.mem]; exact Frame.refl _ _)
    (fun _ h => nomatch h) fun _ _ _ h => nomatch h

theorem Sim.tabS {G : Hash} {g : Impl.RsaOaep.RISCV64.Fns} {j : Nat} (T : TabS G g j Sp s (stackArg s j)) :
    TabS G g j Sp u (stackArg u j) := by
  rw [h.arg]
  exact T.transfer h.1.sp h.1.rd h.2 (by simp only [SC, Sp, h.arg]) (rs := []) (by rw [h.1.mem]; exact Frame.refl _ _)
    (fun _ h => nomatch h) fun _ _ _ h => nomatch h

end

theorem Sim.trans {s u u' : State} (h : Sim s u) (h' : Sim u u') : Sim s u' :=
  ⟨(h.1.trans h'.1).mono fun r hr => by revert r; decide,
    h'.2.trans h.2⟩

/-! ## The index -/

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

theorem idxA_wp {t : State} (h : Sim s t) :
    WP isa (.block [.addSp .t5 (8 * 6), .load .d .t5 .t5 0]) t fun u => Sim s u ∧ u.gpr .t5 = stackArg s 6 :=
  WP.of_syms (wp_addSp (imm := 8 * 6) fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s 6)
    (by rw [e₁, BitVec.add_zero, h.1.sp]; rfl) (arg_al P (by decide))
    ⟨aR s, by rw [o₁.rd, h.1.rd, P.hrd]; simp, in_aR (by decide)⟩
    (fun u₂ o₂ e₂ => wp_nil fun y => ⟨⟨(h.1.trans (o₁.trans o₂)).mono fun r hr => by
      revert r; decide, y.trans h.2⟩,
      by rw [e₂, o₁.mem, h.1.mem]; rfl⟩))

theorem idxB_wp {t : State} (h : Sim s t) (h5 : t.gpr .t5 = stackArg s 6) :
    WP isa (.block [.load .d .t5 .t5 40]) t fun u =>
      Sim s u ∧ u.gpr .t5 = s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 :=
  WP.of_syms (wp_ld (a := stackArg s 6 + BitVec.ofNat 64 40) (by rw [h5])
    (by
      have e : (stackArg s 6 + BitVec.ofNat 64 40).toNat = (stackArg s 6).toNat + 40 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := P.wth; omega_using [this]
      rw [e]; have := P.al6; omega_using [this])
    ⟨tHR s, by rw [h.1.rd, P.hrd]; simp,
      Offset.contains_base (stackArg s 6) (by decide) (by decide)⟩
    (fun u o e => wp_nil fun y => ⟨⟨(h.1.trans o).mono fun r hr => by
      revert r; decide, y.trans h.2⟩,
      by rw [e, h.1.mem]⟩) (by decide))

theorem idxLoad_wp : WP isa (.block (idxLoad 6)) s fun u =>
    Sim s u ∧ u.gpr .t5 = s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 := by
  show WP isa (.block ([.addSp .t5 (8 * 6), .load .d .t5 .t5 0] ++ [.load .d .t5 .t5 40])) s _
  rw [WP.block_append_iff]
  exact WP.mono (idxA_wp P ⟨Only.refl _ s, rfl⟩) fun u ⟨h, e⟩ => idxB_wp P h e

end

/-! ## The code for a hash function's shape -/

/-- The code depends on the hash function only through its shape. -/
theorem verifyFor_shape {H H' : Hash} (hb : H.b = H'.b) (hN : H.N = H'.N) (hD : H.D = H'.D) (be : Bool)
    (f : MdFns) (g : Impl.RsaOaep.RISCV64.Fns) : verifyFor H be f g = verifyFor H' be f g := by
  obtain ⟨b, N, D, _, _, _, _, _, _, _⟩ := H
  obtain ⟨b', N', D', _, _, _, _, _, _, _⟩ := H'
  simp only at hb hN hD
  subst hb hN hD
  rfl

/-- The shape of `v`'s hash function and its byte order are those of its index, one of `idxs`. -/
def Shape (v : MVar) : Prop :=
  idx v ∈ idxs ∧ v.w.H.b = (ofIdx (idx v)).b ∧ v.w.H.N = (ofIdx (idx v)).N ∧ v.w.H.D = (ofIdx (idx v)).D ∧
    v.M.be = beOf (idx v)

instance (v : MVar) : Decidable (Shape v) := by unfold Shape; infer_instance

/-- What the registration checks of the tables: the functions of the same
name have the same code, every hash function has its index's shape, and
there are fewer than `2^32` names. -/
def OK (vs : List MVar) (gs : List MVar) : Prop :=
  Coh vs ∧ MdHashTable.RISCV64.Coh gs ∧ (∀ v ∈ vs, Shape v) ∧
    (names vs ++ MdHashTable.RISCV64.names gs).length < 2 ^ 32 ∧ vs ≠ [] ∧ gs ≠ []

instance (vs : List MVar) (gs : List MVar) : Decidable (OK vs gs) := by unfold OK; infer_instance

theorem shape_code {v : MVar} (hv : Shape v) (f : MdFns) (g : Impl.RsaOaep.RISCV64.Fns) :
    verifyFor (ofIdx (idx v)) (beOf (idx v)) f g = verifyFor v.w.H v.M.be f g := by
  rw [hv.2.2.2.2, verifyFor_shape hv.2.1.symm hv.2.2.1.symm hv.2.2.2.1.symm]

theorem idx_lt {v : MVar} (hv : Shape v) : idx v < 2 ^ 64 := by
  have := hv.1
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at this
  omega_using [this]

/-! ## The tables on entry -/

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

theorem tabM_entry {vs : List MVar} (hc : Coh vs)
    (hpw : (names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {v : MVar} (hv : v ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s (tableOf v))) :
    TabM v.M (digName v) (fnsOf vs) 6 Sp s (stackArg s 6) := by
  refine tabM_of (by decide) rfl (arg_al P (by decide)) P.al6 (show (stackArg s 6).toNat + 40 ≤ 2 ^ 64 by have := P.wth; omega_using [this]) (A := aR s)
    (by rw [P.hrd]; simp) (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; iterate 5 apply List.mem_cons_of_mem
        exact List.mem_cons_self ..) P.kth (P.sth.sub_left (sc_sub P)) hc hpw hv hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega_using [])

theorem tabS_entry {gs : List MVar} (hc : MdHashTable.RISCV64.Coh gs)
    (hpw : (MdHashTable.RISCV64.names gs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : MVar} (hw : w ∈ gs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (MdHashTable.RISCV64.tableOf w))) :
    TabS w.w.H (MdHashTable.RISCV64.fns3 gs) 7 Sp s (stackArg s 7) := by
  refine MdHashTable.RISCV64.tabS_of (by decide) rfl (arg_al P (by decide)) P.al7 P.wtg (A := aR s)
    (by rw [P.hrd]; simp) (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; iterate 6 apply List.mem_cons_of_mem
        exact List.mem_cons_self ..) P.ktg (P.stg.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega_using [])

end

/-- The tables of the hash function's `VT`. -/
def vtOf (vs : List MVar) (gs : List MVar) (v : MVar) (w : MVar) : VT :=
  ⟨v.w.H, v.w.l.ok, v.M, digName v, fnsOf vs, w.w.H, MdHashTable.RISCV64.fns3 gs⟩

theorem vt_names {vs : List MVar} {gs : List MVar} {v : MVar} {w : MVar} (hv : v ∈ vs) (hw : w ∈ gs) :
    ∀ n ∈ (vtOf vs gs v w).names, n ∈ names vs ++ MdHashTable.RISCV64.names gs := by
  have a := Proof.MdHashTable.RISCV64.mem_names hv
  have b := MdHashTable.RISCV64.mem_names hw
  intro n hn
  simp only [VT.names, vtOf, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [List.mem_append_left _ a.1, List.mem_append_left _ a.2.1, List.mem_append_left _ a.2.2.1,
    List.mem_append_left _ a.2.2.2.1, List.mem_append_left _ a.2.2.2.2, List.mem_append_right _ b.1,
    List.mem_append_right _ b.2.1, List.mem_append_right _ b.2.2.1]

/-! ## Correctness -/

/-- The code, from an entry state meeting the contract. -/
theorem code_correct {vs : List MVar} {gs : List MVar} (hok : OK vs gs) (s : State)
    (h : (verSpec (tables vs) (MdHashTable.RISCV64.tables gs)).pre s) :
    ∃ t s', Exec isa (verifyPrecomputed (fnsOf vs) (MdHashTable.RISCV64.fns3 gs)) s t s' ∧ abiPreserved s s' ∧
      (verSpec (tables vs) (MdHashTable.RISCV64.tables gs)).post s s' := by
  obtain ⟨⟨TH, hTH, hhH⟩, ⟨TG, hTG, hhG⟩, hpw⟩ := spec_tab h
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTG
  obtain ⟨hcv, hcg, hsh, -⟩ := hok
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := hpw.sublist (List.sublist_append_right _ _)
  obtain ⟨hmH, hiH⟩ := held_tableOf hhH
  have hH := hashAt_tableOf hiH
  have hG := MdHashTable.RISCV64.hashAt_tableOf (MdHashTable.RISCV64.held_tableOf hhG).2
  have P : PreP v.w.l.G.len s := preP_of h hH
  have T := tabM_entry P hcv hpwH hv hhH
  have TG := tabS_entry P hcg hpwG hw hhG
  have hS := hsh v hv
  have key : WP isa (verifyPrecomputed (fnsOf vs) (MdHashTable.RISCV64.fns3 gs)) s (Post v.w.l.G w.w.l.G s) := by
    refine WP.seq (WP.mono (idxLoad_wp P) fun u ⟨hu, e5⟩ => ?_)
    refine byIdx_ok (I := idx v) (idx_lt hS) (F := fun u => Sim s u ∧ u.gpr .t5 = BitVec.ofNat 64 (idx v))
      (fun _ h => h.2) (fun t t' ⟨h, e⟩ o y => ⟨h.trans ⟨o.mono fun r hr => by
          revert r; decide, y⟩, by rw [o.get .t5, e]⟩)
      (fun u ⟨hu, _⟩ => ?_) hS.1 (fun x hx => (idx_certs x hx).1) u ⟨hu, by rw [e5, hiH]⟩
    rw [shape_code hS]
    exact WP.mono (code_ok (hu.preP P) v.w.l.ok v.w.l.fits (hu.tabM T) v.w.l.hash v.w.l.len v.w.l.valid w.w.l.ok
      w.w.l.fits (hu.tabS TG) w.w.l.hash w.w.l.len w.w.l.valid) fun s' q => hu.post q
  obtain ⟨t, s', he, habi, hr⟩ := key
  refine ⟨t, s', he, habi, ?_⟩
  unfold verSpec
  sig_post [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Abi.withTables, abi, argRegs, stackArgs_eight, List.append_eq]
  intro H' G' hH' hG' hc
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [hr hc]
  unfold vOut
  split <;> rfl

/-! ## Constant time -/

theorem idxA_taint {α : Type} {Φ : α → State → Prop} (h : Pins Φ []) :
    RelCT isa (Two Φ) (.block [.addSp .t5 (8 * 6), .load .d .t5 .t5 0]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem idxB_taint {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.t5]) :
    RelCT isa (Two Φ) (.block [.load .d .t5 .t5 40]) fun _ _ => True :=
  two_taint [.t5] h (by taint_decide)

/-- Two runs from entry states meeting the contract with the same public
data: through the anchor `s₁`, whose tables both have. -/
theorem code_constantTime {vs : List MVar} {gs : List MVar} (hok : OK vs gs) :
    ConstantTime isa (verSpec (tables vs) (MdHashTable.RISCV64.tables gs)).pre
      (verSpec (tables vs) (MdHashTable.RISCV64.tables gs)).pub
      (verifyPrecomputed (fnsOf vs) (MdHashTable.RISCV64.fns3 gs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨TH, hTH, hhH₁⟩, ⟨TG, hTG, hhG₁⟩, hpw₁⟩ := spec_tab h₁
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTG
  obtain ⟨p, hsy, iffH, iffG⟩ := pubP_of hp
  have hhH₂ := (iffH _ hTH).mp hhH₁
  have hhG₂ := (iffG _ hTG).mp hhG₁
  have hpw₂ := (spec_tab h₂).2.2
  obtain ⟨hcv, hcg, hsh, -⟩ := hok
  have hS := hsh v hv
  let W := vtOf vs gs v w
  let D := v.w.l.G.len
  -- Each run's entry.
  have ent : ∀ {s : State}, (verSpec (tables vs) (MdHashTable.RISCV64.tables gs)).pre s →
      Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s (tableOf v)) →
      Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (MdHashTable.RISCV64.tableOf w)) →
      (names vs ++ MdHashTable.RISCV64.names gs).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) →
      PreT D W s ∧ s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx v) :=
    fun {s} h hh hg hpw => by
      have hH := hashAt_tableOf (held_tableOf hh).2
      have P : PreP D s := preP_of h hH
      exact ⟨⟨P, tabM_entry P hcv (hpw.sublist (List.sublist_append_left _ _)) hv hh,
        tabS_entry P hcg (hpw.sublist (List.sublist_append_right _ _)) hw hg⟩, (held_tableOf hh).2⟩
  obtain ⟨P₁, i₁⟩ := ent h₁ hhH₁ hhG₁ hpw₁
  obtain ⟨P₂, i₂⟩ := ent h₂ hhH₂ hhG₂ hpw₂
  have hk : ∀ {s : State}, PreT D W s → 1 ≤ kk s := fun P => Nat.le_trans (by decide) P.1.k1
  let Φ₀ := fun (a s : State) => PreT D W s ∧ PubT W a s ∧
    s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx v)
  let Φ := fun (a u : State) => ∃ s, Φ₀ a s ∧ Sim s u ∧ u.gpr .t5 = BitVec.ofNat 64 (idx v)
  have hct : RelCT isa (Two Φ₀) (verifyPrecomputed (fnsOf vs) (MdHashTable.RISCV64.fns3 gs)) fun _ _ => True := by
    refine RelCT.seq (two_post (Ψ := Φ) ?_ fun a s hs => WP.mono (idxLoad_wp hs.1.1) fun u ⟨h, e⟩ =>
      ⟨s, hs, h, by rw [e, hs.2.2]⟩) ?_
    · -- The index's load.
      let Ψ := fun (a u : State) => ∃ s, Φ₀ a s ∧ Sim s u ∧ u.gpr .t5 = stackArg a 6
      show RelCT isa _ (.block ([.addSp .t5 (8 * 6), .load .d .t5 .t5 0] ++ [.load .d .t5 .t5 40])) _
      refine RelCT.block_append (RelCT.seq (two_post (Ψ := Ψ) (idxA_taint fun a s₁ s₂ h₁ h₂ =>
          ⟨h₁.2.1.1.1.sp.trans h₂.2.1.1.1.sp.symm, fun _ h => nomatch h⟩)
        fun a s hs => WP.mono (idxA_wp hs.1.1 ⟨Only.refl _ s, rfl⟩) fun u ⟨h, e⟩ =>
          ⟨s, hs, h, by rw [e, hs.2.1.1.1.args 6 (by decide) (by decide)]⟩)
        (idxB_taint fun a u₁ u₂ ⟨s₁, x₁, k₁, f₁⟩ ⟨s₂, x₂, k₂, f₂⟩ => ⟨by
          rw [k₁.1.sp, k₂.1.sp]; exact x₁.2.1.1.1.sp.trans x₂.2.1.1.1.sp.symm, fun r hr => by
          rw [List.mem_singleton.mp hr, f₁, f₂]⟩))
    -- The code for the index's shape.
    refine byIdx_ct (I := idx v) (idx_lt hS) (fun a u h => let ⟨_, _, _, e⟩ := h; e)
      (fun a u₁ u₂ ⟨s₁, x₁, k₁, _⟩ ⟨s₂, x₂, k₂, _⟩ => by
        rw [k₁.1.sp, k₂.1.sp]; exact x₁.2.1.1.1.sp.trans x₂.2.1.1.1.sp.symm)
      (fun a u u' ⟨s, x, k, e⟩ o y => ⟨s, x, k.trans ⟨o.mono fun r hr => by
          revert r; decide, y⟩, by rw [o.get .t5, e]⟩) ?_ hS.1 idx_certs
    rw [shape_code hS]
    refine (code_ct (W := W) v.w.l.ct v.w.l.fits v.w.l.len w.w.l.ok w.w.l.ct w.w.l.fits w.w.l.hash w.w.l.len w.w.l.valid
      v.w.l.hash v.w.l.valid).mono (fun u₁ u₂ ⟨a, ⟨s₁, x₁, k₁, _⟩, ⟨s₂, x₂, k₂, _⟩⟩ => ⟨a, ?_, ?_⟩)
      fun _ _ h => h
    · exact ⟨⟨k₁.preP x₁.1.1, k₁.tabM x₁.1.2.1, k₁.tabS x₁.1.2.2⟩, ⟨k₁.pubP x₁.2.1.1.1,
        hk ⟨k₁.preP x₁.1.1, k₁.tabM x₁.1.2.1, k₁.tabS x₁.1.2.2⟩⟩, fun n hn => by rw [k₁.2]; exact x₁.2.1.2 n hn⟩
    · exact ⟨⟨k₂.preP x₂.1.1, k₂.tabM x₂.1.2.1, k₂.tabS x₂.1.2.2⟩, ⟨k₂.pubP x₂.2.1.1.1,
        hk ⟨k₂.preP x₂.1.1, k₂.tabM x₂.1.2.1, k₂.tabS x₂.1.2.2⟩⟩, fun n hn => by rw [k₂.2]; exact x₂.2.1.2 n hn⟩
  exact hct s₁ s₂ t₁ t₂ s₁' s₂' ⟨s₁, ⟨P₁, ⟨⟨pubP_refl s₁, hk P₁⟩, fun _ _ => rfl⟩, i₁⟩,
    ⟨P₂, ⟨⟨p, hk P₂⟩, fun n hn => (hsy n (vt_names hv hw n hn)).symm⟩, i₂⟩⟩ e₁ e₂

end VG.Proof.RsaPss.RISCV64
