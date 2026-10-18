module

public import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCT
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCT

/-!
# `vg_rsa_check_key` on AArch64: constant time, `main`

The pieces of `CkCT.lean` in sequence: the phases of the checks
(`ckPQ_ct`, `ckMod_ct`, `ckQIC_ct`), and `main` (`ckMain_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG.Impl.Rsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The checks modulo `X - 1`. -/
theorem ckMod_ct {sX sXlen sDX sYlen : Nat} (hsX : sX < 32) (hsL : sXlen < 32) (hsD : sDX < 32) (pX pDX : CkP → Addr)
    (xl : CkP → Nat)
    (hX : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sX) = pX I.pub ∧
      word s.mem I.B (8 * sXlen) = BitVec.ofNat 64 (xl I.pub) ∧
      (∃ bs, Src s I.B I.Z (pX I.pub) bs ∧ bs.length = xl I.pub) ∧ 1 ≤ xl I.pub ∧ xl I.pub ≤ I.cap)
    (hDX : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sDX) = pDX I.pub ∧
      word s.mem I.B (8 * sXlen) = BitVec.ofNat 64 (xl I.pub) ∧
      (∃ bs, Src s I.B I.Z (pDX I.pub) bs ∧ bs.length = xl I.pub) ∧ 1 ≤ xl I.pub ∧ xl I.pub ≤ I.cap)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htX : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base aM .x8 ++ [ldh .x1 sX, ldh .x2 sXlen]))
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htDX : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base aX .x8 ++ [ldh .x1 sDX, ldh .x2 sXlen]))
      hc₂).isSome = true)
    (hsY : sYlen < 32) (yl : CkP → Nat)
    (hY : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I →
      word s.mem I.B (8 * sYlen) = BitVec.ofNat 64 (yl I.pub) ∧ yl I.pub ≤ I.cap)
    {h₃ h₄ h₅ : VG.Taint.Hint VG.AArch64.Taint.T}
    (tHi : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ topD sYlen ++ base aA .x16 ++ base aRem .x17 ++ CheckCrtKey.hiTail)) h₃).isSome = true)
    (tLo : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ topD sYlen ++ base aA .x16 ++ base CheckCrtKey.aQ .x17 ++ CheckCrtKey.loTail)) h₄).isSome = true)
    (tCnt : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ topD sYlen ++ CheckCrtKey.cntTail)) h₅).isSome = true) :
    RelCT isa (Two GK) (seqs (modChecks sX sXlen sDX sYlen)) (Two GK) := by
  rw [modChecks_eq]
  have ldX := toGK (ofGK (ld_ct (j := aM) (by decide) hsX hsL pX xl (by decide) hX (by taint_decide) htX (by taint_decide)))
  have ldDX := ofGK (ld_ct (j := aX) (by decide) hsD hsL pDX xl (by decide) hDX (by taint_decide) htDX (by taint_decide))
  have ldD := ofGK (ld_ct (j := aX) (by decide) (by decide) (by decide) CkP.pD CkP.dl (by decide)
    (fun I m₀ s hs L => ⟨hs.args.d, hs.args.dl, ⟨_, hs.d, L.dbl⟩, L.dl1, L.dcap⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))
  have mE := mulE_ckct (by taint_decide) (by taint_decide)
  have rD : RelCT isa (Two GK) (seqs (CheckCrtKey.modOne (topD sYlen))) (Two GK) :=
    modOneTop_ckct (fun p => (yl p + 7) / 8 + 1)
      (fun p s h => by
        obtain ⟨I, m₀, c, rfl, hs, L, _⟩ := h
        obtain ⟨a, b⟩ := hY I m₀ s hs L
        exact topD_ok hsY a (by have := L.cap2; have := L.k2; omega) hs.ws.h256)
      (fun p s h => by
        obtain ⟨I, m₀, c, rfl, hs, L, _⟩ := h
        have := (hY I m₀ s hs L).2
        have := L.cap1
        change 1 ≤ (yl I.pub + 7) / 8 + 1 ∧ (yl I.pub + 7) / 8 + 1 < wW I.cap
        unfold wW wk; omega) tHi tLo tCnt
  have rE : RelCT isa (Two GK) (seqs (CheckCrtKey.modOne CheckCrtKey.topE)) (Two GK) :=
    modOneTop_ckct (fun _ => 1) (fun p s _ => topE_ok p.B p.Z s.mem)
      (fun p s h => by obtain ⟨I, m₀, c, rfl, hs, L, _⟩ := h; simp only [CkIn.pub, wW]; omega)
      (by taint_decide) (by taint_decide) (by taint_decide)
  exact ct_app (by simp [loadA]) (by simp) ldX (ct_app (a := [.block (decA aM)]) (by simp) (by simp [loadA])
    (ct_one (decA_ckct (by decide) (by taint_decide)))
    (ct_app (by simp [loadA]) (by simp [ltA]) ldDX
    (ct_app (by simp [ltA]) (by simp [loadA]) (toGK (ltA_ckct (a := aX) (b := aM) (js := [aX]) (by decide)
      (by decide) (by decide) (by taint_decide)))
    (ct_app (by simp [loadA]) (by simp [mulE]) ldD
    (ct_app (by simp [mulE]) (by simp [CheckCrtKey.modOne, CheckCrtKey.reduceTop]) mE
    (ct_app (by simp [CheckCrtKey.modOne, CheckCrtKey.reduceTop]) (by simp [loadA]) rD
    (ct_app (by simp [loadA]) (by simp [mulE]) ldDX
    (ct_app (by simp [mulE]) (by simp [CheckCrtKey.modOne, CheckCrtKey.reduceTop]) mE rE))))))))

/-! ## `main` -/

/-- On entry to `main`. -/
def GKM (p : CkP) (s : State) : Prop := ∃ I : CkIn, I.pub = p ∧ CkPre I s ∧ I.cap = I.k

theorem pins_GKM : Pins GKM [.x0] := fun _ _ _ ⟨_, e₁, h₁, _⟩ ⟨_, e₂, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.x0, h₂.x0]
  exact (congrArg CkP.B e₁).trans (congrArg CkP.B e₂).symm

theorem ckHead_ct : RelCT isa (Two GKM) (.block VG.Impl.Rsa.AArch64.CheckKey.head) (Two GK) :=
  two_piece [.x0] pins_GKM (by taint_decide) fun _ s ⟨I, e, h, hc⟩ =>
    WP.mono (ckHeadS_ok h hc) fun _ ⟨ht, hm⟩ => ⟨I, s.mem, true, e, ht, h.L, hm⟩

/-- `main` leaks the same in two runs with the same public data. -/
theorem ckMain_ct : RelCT isa (Two GKM) VG.Impl.Rsa.AArch64.CheckKey.main fun _ _ => True := by
  rw [ckMain_eq]
  refine (ct_app (by simp) (by simp [loadA]) (ct_one ckHead_ct)
    (ct_app (by simp [loadA]) (by simp [loadA]) (toGK (ofGK (ldWide_ct (by decide) (by decide) (by decide) CkP.pN CkP.k
      (by decide) (fun I m₀ s hs L => ⟨hs.args.n, hs.args.k, ⟨_, hs.n, L.nl⟩, show 1 ≤ I.k by have := L.k1; omega, Nat.le_refl _⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp [loadA]) (by simp) (toGK (ofGK (ldWide_ct (by decide) (by decide) (by decide) CkP.pE CkP.el
      (by decide) (fun I m₀ s hs L => ⟨hs.args.e, hs.args.el, ⟨_, hs.e, L.ebl⟩, L.el1, L.el2⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp) (by simp [loadA]) (ct_cons (by simp) (zeroA_ckct (by decide) (by taint_decide))
      (ct_one (setOneA_ckct (by decide) (by taint_decide))))
    (ct_app (by simp [loadA]) (by simp [loadA]) ckDN_ct
    (ct_app (by simp [loadA]) (by simp [modChecks]) ckPQ_ct
    (ct_app (by simp [modChecks]) (by simp [modChecks]) (ckMod_ct (by decide) (by decide) (by decide) CkP.pP CkP.pDp
      CkP.pl (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, L.pcap⟩)
      (fun I m₀ s hs L => ⟨hs.args.dp, hs.args.pl, ⟨_, hs.dp, L.dpbl⟩, L.pl1, L.pcap⟩)
      (by taint_decide) (by taint_decide)
      (by decide) CkP.ql (fun I m₀ s hs L => ⟨hs.args.ql, L.qcap⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))
    (ct_app (by simp [modChecks]) (by simp [loadA]) (ckMod_ct (by decide) (by decide) (by decide) CkP.pQ CkP.pDq
      CkP.ql (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, L.qcap⟩)
      (fun I m₀ s hs L => ⟨hs.args.dq, hs.args.ql, ⟨_, hs.dq, L.dqbl⟩, L.ql1, L.qcap⟩)
      (by taint_decide) (by taint_decide)
      (by decide) CkP.pl (fun I m₀ s hs L => ⟨hs.args.pl, L.pcap⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))
    (ct_app (by simp [loadA]) (by simp) ckQIC_ct (ct_one retMaskK_ct)))))))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Rsa.AArch64
