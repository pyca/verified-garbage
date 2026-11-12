module
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTDefs
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyWord
public import VerifiedGarbage.Proof.Rsa.X86_64.WordInitCT

import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTLoads
import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTPieces
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.WordFastCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTDefs
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyWord
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordInitCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTLoads
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTPieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordFastCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_check_key` on x86-64: constant time of the word-level checks

The guard reads only public values (the lengths, `n`'s first byte), so both
runs take the same branch (`guard_ct`); the word-level checks' pieces run
from registers pinned after `ws` or the header loads, and keep `KK`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

theorem KS.room {p : KPub} {s : State} (h : KS p s) : WRoom s p.B p.Z p.w :=
  ⟨h.hS, by have := h.word_room; omega_arith, h.word_w1, h.word_w2⟩

theorem KK.ws {p : KPub} {t : State} (h : KK p t) : Ws t p.B p.Z p.w :=
  let ⟨_, _, _, c, hs⟩ := h; c.ws hs.room

theorem KK.z17 {p : KPub} {t : State} (h : KK p t) : slot p.w 17 ≤ p.Z :=
  let ⟨_, _, _, _, hs⟩ := h; hs.room.hZ

theorem KK.w4 {p : KPub} {t : State} (h : KK p t) : 6 ≤ p.w :=
  let ⟨_, _, _, _, hs⟩ := h; hs.word_w1

theorem KK.frm {p : KPub} {t t' : State} (h : KK p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (ha : ∀ r ∈ rs, Away p.w r) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (hk : Keep mmRegs t t') : KK p t' :=
  let ⟨s, minv, N, c, hs⟩ := h; ⟨s, minv, N, c.frm hf ha hz hk, hs⟩

/-- `copyA o a` into array 5 or 9. -/
theorem copyAK_ct {o a : Nat} (ho : o = 5 ∨ o = 9) (ha : a < 8) (hoa : o ≠ a) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (Impl.Rsa.X86_64.Keys.base a .rsi ++
      Impl.Rsa.X86_64.Keys.base o .rbx)) Impl.Rsa.X86_64.copyWords) hc).isSome = true) :
    RelCT isa (Two KK) (Impl.Rsa.X86_64.Keys.copyA o a) (Two KK) := by
  have e : Impl.Rsa.X86_64.Keys.copyA o a = .seq (.block (Impl.Rsa.X86_64.Keys.ws ++
      (Impl.Rsa.X86_64.Keys.base a .rsi ++ Impl.Rsa.X86_64.Keys.base o .rbx))) Impl.Rsa.X86_64.copyWords := by
    simp only [Impl.Rsa.X86_64.Keys.copyA, List.append_assoc]
  rw [e]
  exact ws_ct KPub.B KPub.Z KPub.w (fun _ _ h => h.ws) ht fun p s h => by
    rw [← e]
    have hZ := h.z17
    exact WP.mono (copyA_ok h.ws (by omega_arith) (by omega_arith) hoa) fun t ⟨_, o', k⟩ =>
      h.frm (Frm.of_outside o' (List.mem_singleton_self _))
        (by simp only [List.mem_singleton, forall_eq]
            rcases ho with rfl | rfl
            · exact away_slot p.w (by decide) (.inl (by decide)) (by omega_arith)
            · exact away_slot p.w (by decide) (.inr (by decide)) (by omega_arith))
        (by simp only [List.mem_singleton, forall_eq]
            rcases ho with rfl | rfl <;> simp only [slot_eq] at hZ ⊢ <;> omega_arith)
        (k.mono (by decide))

/-- `WordDivide`'s normalization and division, of the dividend's words `top` gives. -/
theorem fastAtK_ct {top : Option Nat} (ck : WordDivide.SeedCk top) (hk : ∀ k, top = some k → k ≤ 3) :
    RelCT isa (Two KK) (.seq (.block Impl.Rsa.X86_64.WordDivide.normalize)
      (Impl.Rsa.X86_64.WordDivide.code top)) (Two KK) :=
  two_post (two_map (fun p : KPub => (⟨p.B, p.Z, p.w, 0⟩ : WordDivide.Pub)) (fun _ _ h => ⟨h.ws, h.z17, h.w4⟩)
    (WordDivide.fastAt_ct ck fun _ k hw e => by have := hk k e; omega_arith)) fun p s h =>
    WP.mono (WordDivide.fastAt_ok h.ws h.z17 h.w4 (fun k e => by have := hk k e; have := h.w4; omega_arith))
      fun _ ⟨_, f, k⟩ =>
      h.frm f (norm_away (by have := h.w4; omega_arith)) (norm_bound (by have := h.w4; omega_arith) h.z17) k

theorem fastK_ct : RelCT isa (Two KK) (.seq (.block Impl.Rsa.X86_64.WordDivide.normalize)
    Impl.Rsa.X86_64.WordDivide.code) (Two KK) :=
  fastAtK_ct WordDivide.seedCk_none fun _ e => nomatch e

theorem eqAK_ct {a b : Nat} (ha : a < 16) (hb : b < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (Impl.Rsa.X86_64.Keys.base a .rbx ++
      (Impl.Rsa.X86_64.Keys.base b .r10 ++ ([.mov32 .rbp (.imm 0)] : List Instr))))
      (wordLoop 0 Impl.Rsa.X86_64.Keys.xorBody)) hc).isSome = true) :
    RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.Keys.eqA a b)) (Two KK) := by
  have e : seqs (Impl.Rsa.X86_64.Keys.eqA a b) = .seq (.block (Impl.Rsa.X86_64.Keys.ws ++
      (Impl.Rsa.X86_64.Keys.base a .rbx ++ (Impl.Rsa.X86_64.Keys.base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 Impl.Rsa.X86_64.Keys.xorBody) := by
    simp only [Impl.Rsa.X86_64.Keys.eqA, seqs, List.append_assoc]
  rw [e]
  exact ws_ct KPub.B KPub.Z KPub.w (fun _ _ h => h.ws) ht fun p s h => by
    rw [← e]
    exact WP.mono (eqA_ok h.ws ha hb) fun _ ⟨_, hm, k⟩ => h.keep hm (k.mono (by decide))

theorem andZeroK_ct : RelCT isa (Two KK) (.block Impl.Rsa.X86_64.Keys.CrtValues.andZero) (Two KK) :=
  two_piece [.rdi] pins_kk (by taint_decide) fun p s h => by
    obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (andZeroK c) fun _ c' => ⟨s₀, minv, N, c', hs⟩

/-! ## The guard -/

/-- The guard's value from the public data. -/
def pubGuard (p : KPub) : BitVec 64 := WordDivide.guardVal p.w p.k p.pl p.ql ((p.nb[0]?).getD 0)

def KGH (p : KPub) (t : State) : Prop := KK p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rdx = p.np

def KGT (p : KPub) (t : State) : Prop := KK p t ∧ t.zf = some (pubGuard p == 0)

theorem guard_ct : RelCT isa (Two KK) (.block guard) (Two KGT) := by
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := KGH) [.rdi] pins_kk (by taint_decide) ?_)
    (two_piece [.rdi, .rdx] ?_ (by taint_decide) ?_))
  · intro p s h
    obtain ⟨s₀, minv, N, c, hs⟩ := id h
    obtain ⟨hdi, hl, hw, -⟩ := h.lds
    exact WP.mono (WP.keep [.r12, .rdx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rdx = p.np ∧
        t.mem = s.mem) (by
      xrun [guardHead, State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl Impl.Bignum.X86_64.Public.sN (by decide), hw,
        c.hdr _ (show Impl.Bignum.X86_64.Public.sN < 32 by decide) (by decide), hs.hN]) rfl)
      fun t ⟨⟨h12, hdx, hm⟩, k⟩ => ⟨h.keep hm (k.mono (by decide)), h12, hdx⟩
  · intro p s₁ s₂ h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.rdi, h₂.1.rdi]
    · rw [h₁.2.2, h₂.2.2]
  · rintro p s ⟨h, h12, hdx⟩
    obtain ⟨s₀, minv, N, c, hs⟩ := id h
    obtain ⟨hdi, hl, -, -⟩ := h.lds
    have sr := c.src hs.srN
    have hnl := hs.nl
    refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = s.mem ∧
      t.zf = some (pubGuard p == 0)) (by
      xrun [guardTail, State.ea, hdr, hdi, h12, hdx, hdrOff,
        hl Impl.Bignum.X86_64.Public.sK (by decide), hl sPlen (by decide), hl sQlen (by decide),
        c.hdr _ (show Impl.Bignum.X86_64.Public.sK < 32 by decide) (by decide), hs.hK,
        c.hdr _ (show sPlen < 32 by decide) (by decide), hs.hPl, c.hdr _ (show sQlen < 32 by decide) (by decide), hs.hQl,
        show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        show InRegions (s.rd ++ s.wr) p.np 1 by simpa using sr.rd 0 hnl,
        show s.mem p.np = (p.nb[0]?).getD 0 from by simpa [List.getElem?_eq_getElem hnl] using sr.val 0 hnl,
        pubGuard, WordDivide.guardVal]
      rfl) rfl) fun t ⟨⟨hm, hz⟩, k⟩ => ⟨h.keep hm (k.mono (by decide)), hz⟩

/-! ## The word-level checks -/

theorem wordRem_ct : RelCT isa (Two KK) (seqs wordRem) (Two KK) := by
  unfold wordRem
  simp only [List.append_assoc]
  refine kk_app (by simp) (by simp) (copyAK_ct (.inr rfl) (by decide) (by decide) (by taint_decide))
    (kk_app (by simp [loadNum]) (by simp) ?_ (kk_app (by simp) (by simp [Impl.Rsa.X86_64.Keys.eqA]) fastK_ct
      (kk_app (by simp [Impl.Rsa.X86_64.Keys.eqA]) (by simp) (eqAK_ct (by decide) (by decide) (by taint_decide))
        andZeroK_ct)))
  exact loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pd) (·.dl)
    (fun _ _ h => ⟨h.hD, h.hDl, h.srD, h.dl1, h.dl2⟩) (by taint_decide) (by taint_decide)

theorem remOne_ct {top : Option Nat} (ck : WordDivide.SeedCk top) (hk : ∀ k, top = some k → k ≤ 3) :
    RelCT isa (Two KK) (seqs (remOne top)) (Two KK) := by
  simp only [remOne, List.append_assoc]
  exact kk_app (by simp) (by simp) (copyAK_ct (.inl rfl) (by decide) (by decide) (by taint_decide))
    (kk_app (by simp) (by simp) (copyAK_ct (.inr rfl) (by decide) (by decide) (by taint_decide))
      (kk_app (by simp) (by simp [Impl.Rsa.X86_64.Keys.eqA]) (fastAtK_ct ck hk)
        (kk_app (by simp [Impl.Rsa.X86_64.Keys.eqA]) (by simp)
          (eqAK_ct (by decide) (by decide) (by taint_decide)) andZeroK_ct)))

/-- `wordMod`, for the factor `X`. -/
theorem wordMod_ct {sX sXlen sDX : Nat}
    (hM : RelCT isa (Two KK) (seqs (loadNum aM sX sXlen)) (Two KK))
    (hDX : RelCT isa (Two KK) (seqs (loadNum aX sDX sXlen)) (Two KK)) :
    RelCT isa (Two KK) (seqs (wordMod sX sXlen sDX)) (Two KK) := by
  simp only [wordMod, List.append_assoc]
  exact kk_app (by simp [loadNum]) (by simp [decM]) hM (kk_app (by simp [decM]) (by simp [loadNum]) decMK_ct
    (kk_app (by simp [loadNum]) (by simp [ltMask]) hDX (kk_app (by simp [ltMask]) (by simp [wordRem]) ltXM
      (kk_app (by simp [wordRem]) (by simp [mulE]) wordRem_ct (kk_app (by simp [mulE])
        (by simp [remOne]) mulEK_ct
        (remOne_ct WordDivide.seedCk_one fun k e => by obtain rfl := Option.some.inj e; decide))))))

theorem wordQInv_ct : RelCT isa (Two KK) (seqs wordQInv) (Two KK) := by
  simp only [wordQInv, List.append_assoc]
  exact kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PM (kk_app (by simp [loadNum]) (by simp [ltMask]) ld_QI
    (kk_app (by simp [ltMask]) (by simp [loadNum]) ltXM (kk_app (by simp [loadNum]) (by simp [mulPQ]) ld_QR
      (kk_app (by simp [mulPQ]) (by simp [remOne]) mulPQK_ct
        (remOne_ct WordDivide.seedCk_none fun _ e => nomatch e)))))

theorem wordChecks_ct : RelCT isa (Two KK) (seqs wordChecks) (Two KK) := by
  unfold wordChecks
  simp only [List.append_assoc]
  exact kk_app (by simp [wordMod, loadNum]) (by simp [wordMod, loadNum])
    (wordMod_ct ld_PM ld_DP)
    (kk_app (by simp [wordMod, loadNum]) (by simp [wordQInv, loadNum])
      (wordMod_ct ld_QM ld_DQ)
      wordQInv_ct)

end VG.Proof.Rsa.X86_64.Key
