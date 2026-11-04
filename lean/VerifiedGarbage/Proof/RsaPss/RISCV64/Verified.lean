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
  sig_pub [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
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
  · rcases (by omega : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl
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
    omega
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
      bytes_entry c₁.base.mem P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega),
      bytes_entry c₂.base.mem P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega), p₁.1.e, p₂.1.e]

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
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
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
    exact ⟨s, P, p, E, y, h0, by rw [p.1.1.pKk, p.1.1.pLoN p.1.2]; omega⟩
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
    omega
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
