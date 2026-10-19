module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
public import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.RvFin3
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # An RSA key on ARMv7: divisions

`divBy q d`: `[q] := [q] / [d]` and `[aDr] := [q] mod [d]` for a nonzero
`[d]`, through the division's divisor `aDv` and temporary `aDt`; the
division leaves `r7` and `r9` changed, which `ctxW` restores.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {P : KP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- A step that writes array `o` but not its number. -/
theorem KS.same1 {o : Nat} (h : KS P σ A live V ls s) (k : Keep P.B P.W [o] [] s.mem t.mem)
    (ho : o < nArr) (e : num t.mem P.B P.W o = num s.mem P.B P.W o)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : KS P σ A live V ls t := by
  refine h.core k (by simpa using ho) (by simp) sp rd wr (fun j hj => ?_) (h.sl_keep k (by simp) (by simp))
    h.live_lt h.ls_ok
  by_cases ej : j = o
  · subst ej; rw [e]; exact h.arrs _ hj
  · rw [k.num (fun i hi ei => ej (by simp only [List.mem_singleton] at hi; rw [← ei, hi])) (by simp)
      (h.pre.fit (h.live_lt j hj))]
    exact h.arrs j hj

/-- `ctxW`: `W` and the stride. -/
theorem KS.ctxW_ok (h : KS P σ A live V ls s) (r8 : s.gpr .r8 = P.B) :
    WP isa (.block ctxW) s fun t => KS P σ A live V ls t ∧ Ws t P.B P.Z P.W nArr := by
  have pre := h.pre
  have hz := pre.hdr_Z
  have hf := pre.fS
  unfold ctxW
  refine wp_ldr (by decide) (by rw [r8]; exact addr_add (by simp only [hdr] at hz; omega))
    ⟨P.rS, List.mem_append_right _ (by rw [h.wr]; exact pre.rS_mem), Offset.contains_base _
      (by simp only [hdr] at hz; omega) (by omega)⟩ fun s1 u1 => ?_
  have e9 : s1.gpr .r9 = BitVec.ofNat 32 P.W := by
    rw [u1.gpr, ← h.cnt]; simp only [slot, w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [← List.append_nil stride]
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by have := pre.wle; omega) e9 fun t h7 r m => WP.block_nil ?_
  have rt : Rest [.r9, .r7] s t := (u1.rest (by simp)).trans (r.mono (by simp))
  have ht : KS P σ A live V ls t := h.of_rest rt (m.trans u1.mem)
  exact ⟨ht, ht.ws h7 (by rw [rt.gpr _ (by decide), r8]) (by rw [r.gpr _ (by decide), e9])⟩

end

section
variable {P : KP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `ctxW` after the division. -/
theorem St.pctxW :
    VP (fun σ s => E σ ∧ KS P σ (A σ) L (V σ) LS s ∧ s.gpr .r8 = P.B) (.block ctxW) (St P E A L V LS) :=
  VP.taint [.r8] ctxW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2, h₂.2.2])
    fun _ _ ⟨e, h, r8⟩ => WP.mono (h.ctxW_ok r8) fun _ ⟨ht, hw⟩ => ⟨e, ht, hw⟩

/-- The divisor's top word cleared and the division's header. -/
theorem St.pdivHdr {q : Nat} (cert : Cert (.block (VG.Impl.Rsa.Arm.Recover.clrW aDv ++
      VG.Impl.Rsa.Arm.CrtValues.divHdr q aDr aDv aDt))) (hq : q < nArr) :
    VP (St P E A L V LS) (.block (VG.Impl.Rsa.Arm.Recover.clrW aDv ++ VG.Impl.Rsa.Arm.CrtValues.divHdr q aDr aDv aDt))
      (fun σ s => St P E A L V LS σ s ∧ DivHdr s.mem P.B P.W q aDr aDv aDt ∧
        w32 s.mem (State.addr P.B) (arr P.W aDv + 4 * P.W) = 0) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    refine VG.Proof.Rsa.Arm.Recover.clrW_ok hw (j := aDv) (by decide) (by decide) fun s1 hw1 k1 n1 z1 r1 => ?_
    have h1 := h.same1 k1 (by decide) n1 r1.sp r1.rd r1.wr
    have c1 : s1.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.W := by
      rw [← h1.cnt]; simp only [slot, w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine VG.Proof.Rsa.Arm.CrtValues.divHdr_ok hw1 (by simp only [nArr] at hq; omega) (by decide) (by decide)
      (by decide) c1 fun t hwt k2 d2 r2 => WP.block_nil ⟨⟨e, ?_, hwt⟩, d2, ?_⟩
    · have hds : ∀ d ∈ ([0, 4, 8, 12] : List Nat), SlotOk d := by decide
      exact h1.core k2 (by simp) hds r2.sp r2.rd r2.wr (h1.arrs_keep k2 (by simp) hds)
        (h1.sl_keep k2 hds fun d hd x => by
          have := (h1.ls_ok d hd).2.1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at x; omega) h1.live_lt h1.ls_ok
    · have fD := h.pre.fit (show aDv < nArr by decide)
      have hS : S P.W = 4 * (P.W + 2) := rfl
      rw [k2.word (by omega) (by simp) (by decide) fD, z1]

/-- The division, of `[q]` by the nonzero `[aDv]`. -/
theorem St.pdiv {q : Nat} (hqN : q < nArr) (hq : q ∈ L) (hD : aDv ∈ L) (hqD : q ≠ aDv) (hqr : q ≠ aDr) (hqt : q ≠ aDt)
    (hr : aDr ∉ L) (ht : aDt ∉ L) (hpos : ∀ σ, E σ → 0 < A σ aDv) :
    VP (fun σ s => St P E A L V LS σ s ∧ DivHdr s.mem P.B P.W q aDr aDv aDt ∧
        w32 s.mem (State.addr P.B) (arr P.W aDv + 4 * P.W) = 0) VG.Impl.Rsa.Arm.Div.code
      (fun σ s => E σ ∧ KS P σ (upd (upd (A σ) q (A σ q / A σ aDv)) aDr (A σ q % A σ aDv)) (aDr :: q :: L) (V σ) LS s ∧
        s.gpr .r8 = P.B) := by
  refine VP.of_ct (fun σ₁ σ₂ => (VG.Proof.Rsa.Arm.Div.code_ct (g := divGeom P.B P.Z P.W q aDr aDv aDt)).mono
    (fun s t h => ⟨divGeom_ctx h.1.1.2.2 hqN (by decide) (by decide) (by decide) hqr hqD hqt (by decide)
      (by decide) (by decide) h.1.2.1,
      divGeom_ctx h.2.1.2.2 hqN (by decide) (by decide) (by decide) hqr hqD hqt (by decide)
      (by decide) (by decide) h.2.2.1⟩) fun _ _ _ => trivial) fun σ s ⟨⟨e, h, hw⟩, hh, top⟩ => ?_
  refine WP.mono (div_ok hw (q := q) (r := aDr) (d := aDv) (t := aDt) hqN (by decide) (by decide)
    (by decide) hqr hqD hqt (by decide) (by decide) (by decide) hh top) fun t ⟨k, r, v⟩ => ⟨e, ?_, ?_⟩
  · have g : ∀ j ∈ L, num s.mem P.B P.W j = A σ j := fun j hj => h.arrs j hj
    obtain ⟨vr, vq⟩ := v (by rw [g aDv hD]; exact hpos σ e)
    rw [g q hq, g aDv hD] at vr vq
    refine h.core k (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hqN
        · decide
        · decide) (by simp) r.sp r.rd r.wr (fun j hj => ?_) (h.sl_keep k (by simp) (by simp))
      (fun j hj => ?_) h.ls_ok
    · simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj
      · rw [upd_self]; exact vr
      · rw [upd_ne _ _ hqr, upd_self]; exact vq
      · have j1 : j ≠ aDr := fun x => hr (x ▸ hj)
        by_cases jq : j = q
        · subst jq; rw [upd_ne _ _ j1, upd_self]; exact vq
        · rw [upd_ne _ _ j1, upd_ne _ _ jq, k.num (fun i hi ei => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl
            · exact jq ei.symm
            · exact j1 ei.symm
            · exact ht (ei ▸ hj)) (by simp) (h.pre.fit (h.live_lt j hj))]
          exact g j hj
    · simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj
      · decide
      · exact hqN
      · exact h.live_lt j hj
  · rw [r.gpr _ (by decide), hw.r8]

/-- `divBy q d`: `[q] := [q] / [d]` and `[aDr] := [q] mod [d]`, for `[d] > 0`. -/
theorem St.pdivBy {q d : Nat} (cd : Cert (copy aDv d)) (ch : Cert (.block (VG.Impl.Rsa.Arm.Recover.clrW aDv ++
      VG.Impl.Rsa.Arm.CrtValues.divHdr q aDr aDv aDt))) (hqN : q < nArr) (hq : q ∈ L) (hd : d ∈ L)
    (hL : ∀ j ∈ L, j ∉ [aDv, aDr, aDt]) (hpos : ∀ σ, E σ → 0 < A σ d) :
    VP (St P E A L V LS) (divBy q d)
      (St P E (fun σ => upd (upd (A σ) q (A σ q / A σ d)) aDr (A σ q % A σ d)) (aDr :: q :: L) V LS) := by
  have nq := hL q hq
  have nd := hL d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at nq nd
  have nr : aDr ∉ L := fun x => by have := hL aDr x; simp at this
  have nt : aDt ∉ L := fun x => by have := hL aDt x; simp at this
  simp only [divBy, seqs]
  refine VP.seq (St.pcopy cd (by decide) hd (Ne.symm nd.1)) ?_
  refine VP.seq (St.pdivHdr ch hqN) ?_
  refine VP.seq (St.pdiv hqN (List.mem_cons_of_mem _ hq) (by simp) nq.1 nq.2.1 nq.2.2
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, nr⟩)
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, nt⟩) fun σ e => by
      rw [upd_self]; exact hpos σ e) ?_
  refine St.pctxW.mono (fun _ _ h => h) fun σ s h => h.mono (fun j hj => ⟨?_, ?_⟩) (fun x hx => ⟨hx, rfl⟩)
  · simp only [List.mem_cons] at hj ⊢
    rcases hj with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr h))
  · have qD : q ≠ aDv := nq.1
    have e1 : upd (A σ) aDv (A σ d) q = A σ q := upd_ne _ _ qD
    have e2 : upd (A σ) aDv (A σ d) aDv = A σ d := upd_self _ _ _
    rw [e1, e2]
    simp only [List.mem_cons] at hj
    rcases hj with rfl | rfl | hj
    · rw [upd_self, upd_self]
    · rw [upd_ne _ _ nq.2.1, upd_self, upd_ne _ _ nq.2.1, upd_self]
    · have j1 : j ≠ aDr := fun x => nr (x ▸ hj)
      have j2 : j ≠ aDv := fun x => by have := hL j hj; rw [x] at this; simp at this
      rw [upd_ne _ _ j1, upd_ne _ _ j1]
      by_cases jq : j = q
      · subst jq; rw [upd_self, upd_self]
      · rw [upd_ne _ _ jq, upd_ne _ _ jq, upd_ne _ _ j2]

end

end VG.Proof.RsaKeyGen.Arm.Key
