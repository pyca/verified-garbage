module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Mgf
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View

/-!
# RSA paddings on PPC64LE: MGF1, twice

Untrusted: everything here is checked by Lean. `round_ct`: two runs of a
round of `mgfXor` from states with `Base` and the same MGF1 registers
(`MgfR`) leak alike: its blocks by the taint analysis, its calls by
`init_ct`, `upd_ct` and `fin_ct`. `mgfXor_ct`: the loop, whose condition
both runs agree on since each satisfies `MgfI` for the same counter
(`round_ok`), for any public data that fix the stack pointer and `S`
(`OkS`), or `Ok`'s.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo Two Pins two_post wp_li wp_addi wp_mov wp_nil eval_nonzero)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

/-- In a round: `B` and MGF1's registers, for the counter `c`. -/
def MgfR (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (Dg src srcLen dst dstLen : Nat) (ac : State × Nat) (t : State) : Prop :=
  B S vf Pre Pub ac.1 t ∧ t.gpr .r24 = off (S ac.1) src ∧ t.gpr .r25 = BitVec.ofNat 64 srcLen ∧
    t.gpr .r26 = off (S ac.1) dst ∧ t.gpr .r27 = BitVec.ofNat 64 dstLen ∧
    t.gpr .r28 = BitVec.ofNat 64 ac.2 ∧ t.gpr .r29 = BitVec.ofNat 64 (ac.2 * Dg) ∧ ac.2 * Dg < dstLen

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  {Dg src srcLen dst dstLen : Nat}

theorem MgfR.keep {ac : State × Nat} {t t' : State} (h : MgfR S vf Pre Pub Dg src srcLen dst dstLen ac t)
    (hb : B S vf Pre Pub ac.1 t') (hg : ∀ r ∈ [Reg.r24, .r25, .r26, .r27, .r28, .r29], t'.gpr r = t.gpr r) :
    MgfR S vf Pre Pub Dg src srcLen dst dstLen ac t' :=
  ⟨hb, (hg _ (by decide)).trans h.2.1, (hg _ (by decide)).trans h.2.2.1, (hg _ (by decide)).trans h.2.2.2.1,
    (hg _ (by decide)).trans h.2.2.2.2.1, (hg _ (by decide)).trans h.2.2.2.2.2.1,
    (hg _ (by decide)).trans h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem mgfR_pins (X : OkS S Pre Pub) {Φ : State × Nat → State → Prop}
    (h : ∀ ac t, Φ ac t → MgfR S vf Pre Pub Dg src srcLen dst dstLen ac t) :
    Pins Φ [.r14, .r26, .r27, .r29] := fun ac t₁ t₂ h₁ h₂ => by
  obtain ⟨b₁, -, -, x26, x27, -, x29, -⟩ := h ac t₁ h₁
  obtain ⟨b₂, -, -, y26, y27, -, y29, -⟩ := h ac t₂ h₂
  refine ⟨(b₁.spS X).trans (b₂.spS X).symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (b₁.r14S X).trans (b₂.r14S X).symm
  exacts [x26.trans y26.symm, x27.trans y27.symm, x29.trans y29.symm]

theorem pins_mono {α : Type} {Φ : α → State → Prop} {rs rs' : List Reg} (h : Pins Φ rs)
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : Pins Φ rs' := fun a t₁ t₂ h₁ h₂ =>
  ⟨(h a t₁ t₂ h₁ h₂).1, fun r hr => (h a t₁ t₂ h₁ h₂).2 r (hs r hr)⟩

theorem mgfR_base {Φ : State × Nat → State → Prop} (h : ∀ ac t, Φ ac t → MgfR S vf Pre Pub Dg src srcLen dst dstLen ac t) :
    ∀ ac t, Φ ac t → B S vf Pre Pub ac.1 t := fun ac t hp => (h ac t hp).1

end

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : OkS S Pre Pub) {G : Hash} (hG : HashOK G) (cG : HashCT hG) {src srcLen dst dstLen : Nat}
  (hf : MFit src srcLen dst dstLen)

/-- Two runs with `B` for anchors agreeing on what an argument is. -/
theorem two_args {Φ : State × Nat → State → Prop} {t₁ t₂ : State} (h : Two Φ t₁ t₂)
    (hb : ∀ ac t, Φ ac t → B S vf Pre Pub ac.1 t) :
    ∃ ac s₁ s₂, Φ ac t₁ ∧ Φ ac t₂ ∧ Pre s₁ ∧ Pub ac.1 s₁ ∧ Base S vf s₁ t₁ ∧ Pre s₂ ∧ Pub ac.1 s₂ ∧
      Base S vf s₂ t₂ := by
  obtain ⟨ac, h₁, h₂⟩ := h
  obtain ⟨s₁, P₁, p₁, b₁⟩ := hb ac t₁ h₁
  obtain ⟨s₂, P₂, p₂, b₂⟩ := hb ac t₂ h₂
  exact ⟨ac, s₁, s₂, h₁, h₂, P₁, p₁, b₁, P₂, p₂, b₂⟩

include X hG hf in
/-- `xorOut` keeps `B`. -/
theorem xorOut_base {ac : State × Nat} {t : State} (h : MgfR S vf Pre Pub G.D src srcLen dst dstLen ac t) :
    WP isa (xorOut G) t (B S vf Pre Pub ac.1) := by
  have F := hfits hG
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hD0 := hG.hD0
  have hD64 := hG.hD64
  have hfd := hf.fd
  obtain ⟨⟨s, P, p, b⟩, -, -, h26, h27, -, h29, hc⟩ := h
  have hdc := Nat.min_le_left G.D (dstLen - ac.2 * G.D)
  have hn0 : 0 < min G.D (dstLen - ac.2 * G.D) := by omega_arith
  refine WP.seq (WP.mono (xorHead_ok (G := G) (S := S s) (dst := dst) (dstLen := dstLen) (done := ac.2 * G.D)
    (by omega) b.r14 (by rw [h26, (X.S p)]) h27 h29 hc (by omega)) fun t₁ ⟨k₁, x11, x12, x9⟩ => ?_)
  have b₁ := b.only (X.fits P) k₁
  refine WP.mono (xorLoop_ok (p := off (S s) (dst + ac.2 * G.D)) (q := off (S s) oDig) hn0 (by omega_arith) x11 x12 x9
    (fun j hj => by
      rw [off_add, k₁.rd, k₁.wr, b.wr, b.rd]; exact sc_inR (X.fits P) (by omega_arith) _)
    (sc_w (X.fits P) (by rw [k₁.wr, b.wr]) (by omega_arith))
    (fun j hj i hi => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith))
    (fun i hi j hj hij => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)))
    fun t₂ ⟨k₂, x₂⟩ => ⟨s, P, p, b₁.wb (X.fits P) k₂ (by rw [xorAt_length]; omega_arith) x₂⟩

include X cG hf in
theorem round_ct :
    RelCT isa (Two (MgfR S vf Pre Pub G.D src srcLen dst dstLen)) (round G) fun _ _ => True := by
  have F := hfits hG
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hfs := hf.fs
  have hfd := hf.fd
  have p0 : ∀ {Φ : State × Nat → State → Prop}, (∀ ac t, Φ ac t → MgfR S vf Pre Pub G.D src srcLen dst dstLen ac t) →
      Pins Φ [] := fun h ac t₁ t₂ h₁ h₂ => ⟨((mgfR_pins X h) ac t₁ t₂ h₁ h₂).1, fun _ h => nomatch h⟩
  let M := MgfR S vf Pre Pub G.D src srcLen dst dstLen
  have pres : ∀ {t t' : State}, (∀ r ∈ preserved, t'.gpr r = t.gpr r) →
      ∀ r ∈ [Reg.r24, .r25, .r26, .r27, .r28, .r29], t'.gpr r = t.gpr r :=
    fun h r hr => h r (by revert r; decide)
  -- `init`.
  refine two_seq (Ψ := fun ac t => M ac t ∧ t.gpr .r3 = off (S ac.1) oSt) (st_taint (p0 fun _ _ h => h))
    (fun ac t h => wp_addi fun t' o e => wp_nil ⟨h.keep (h.1.onlyS X o) (fun r hr => o.gpr r (by revert r; decide)),
      by obtain ⟨⟨s, _, p, b⟩, _⟩ := h; rw [e, b.r14, (X.S p)]⟩) ?_
  refine two_seq (Ψ := M) (init_ct (S := S) (vf := vf) cG fun t₁ t₂ hp => ?_) (fun ac t h => ?_) ?_
  · obtain ⟨ac, s₁, s₂, h₁, h₂, P₁, p₁, b₁, P₂, p₂, b₂⟩ := two_args hp fun ac t h => h.1.1
    exact ⟨s₁, s₂, X.fits P₁, b₁, by rw [h₁.2, (X.S p₁)], X.fits P₂, b₂, by rw [h₂.2, (X.S p₂)], h₁.2.trans h₂.2.symm,
      (Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm⟩
  · obtain ⟨hm, h3⟩ := h
    obtain ⟨s, P, p, b⟩ := hm.1
    exact WP.mono (init_ok (X.fits P) hG b (by rw [h3, (X.S p)])) fun t' ⟨b', g', _⟩ => hm.keep ⟨s, P, p, b'⟩ (pres g')
  -- `update` with `src`.
  let U₁ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .r3 = off (S ac.1) oSt ∧
    t.gpr .r4 = 0 ∧ t.gpr .r5 = off (S ac.1) src ∧ t.gpr .r6 = BitVec.ofNat 64 srcLen ∧
    t.gpr .r7 = off (S ac.1) oW
  refine two_seq (Ψ := U₁) (r2_taint (p0 fun _ _ h => h)) (fun ac t h => ?_) ?_
  · refine wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ =>
      wp_mov fun t₄ o₄ e₄ => wp_addi fun t₅ o₅ e₅ => wp_nil ?_
    have k : Only [.r3, .r4, .r5, .r6, .r7] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
    obtain ⟨s, P, p, b⟩ := h.1
    refine ⟨h.keep (h.1.onlyS X k) (fun r hr => k.gpr r (by revert r; decide)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₅.get .r3, o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, b.r14, (X.S p)]
    · rw [o₅.get .r4, o₄.get .r4, o₃.get .r4, e₂]; rfl
    · rw [o₅.get .r5, o₄.get .r5, e₃, o₂.get .r24, o₁.get .r24, h.2.1]
    · rw [o₅.get .r6, e₄, o₃.get .r25, o₂.get .r25, o₁.get .r25, h.2.2.1]
    · rw [e₅, o₄.get .r14, o₃.get .r14, o₂.get .r14, o₁.get .r14, b.r14, (X.S p)]
  have uargs : ∀ {ac : State × Nat} {t : State}, U₁ ac t →
      ∃ s, Pre s ∧ UpdArgs S vf G s t (off (S s) src) srcLen ∧ Pub ac.1 s := fun {ac t} h => by
    obtain ⟨hm, h3, -, h5, h6, h7⟩ := h
    obtain ⟨s, P, p, b⟩ := hm.1
    exact ⟨s, P, ⟨X.fits P, b, by rw [h3, (X.S p)], by rw [h5, (X.S p)], by rw [h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
      by rw [h7, (X.S p)], Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) (by omega)),
      sdis (.inl (by omega_arith)) (by omega_arith) (by omega_arith), sdis (.inl (by omega_arith)) (by omega_arith) (by omega_arith),
      cR_dis (X.fits P) (by omega_arith)⟩, p⟩
  refine two_seq (Ψ := M) (upd_ct (S := S) (vf := vf) cG fun t₁ t₂ ⟨ac, h₁, h₂⟩ => ?_) (fun ac t h => ?_) ?_
  · obtain ⟨s₁, -, A₁, p₁⟩ := uargs h₁
    obtain ⟨s₂, -, A₂, p₂⟩ := uargs h₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm, h₁.2.2.2.2.2.trans h₂.2.2.2.2.2.symm]
  · obtain ⟨s, P, A, p⟩ := uargs h
    exact WP.mono (upd_ok A.P hG A.b A.h3 A.h5 A.h6 A.h7 A.hdc A.hd₁ A.hd₂ A.hd₃) fun t' ⟨b', g', _⟩ =>
      h.1.keep ⟨s, P, p, b'⟩ (pres g')
  -- The counter, and `update` with it.
  let U₂ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .r3 = off (S ac.1) oSt ∧
    t.gpr .r4 = BitVec.ofNat 64 srcLen ∧ t.gpr .r5 = off (S ac.1) oCtr ∧ t.gpr .r6 = BitVec.ofNat 64 4 ∧
    t.gpr .r7 = off (S ac.1) oW
  have hD0 := hG.hD0
  refine two_seq (Ψ := U₂) (ctr_taint (pins_mono (mgfR_pins X fun _ _ h => h))) (fun ac t h => ?_) ?_
  · obtain ⟨s, P, p, b⟩ := h.1
    have hc : ac.2 < 2 ^ 32 := by
      have := h.2.2.2.2.2.2.2; have := Nat.le_mul_of_pos_right ac.2 hD0; omega_arith
    exact WP.mono (ctr_ok (X.fits P) b h.2.2.2.2.2.1 hc) fun t' ⟨b', g', _, x3, x4, x5, x6, x7⟩ =>
      ⟨h.keep ⟨s, P, p, b'⟩ (pres g'), by rw [x3, (X.S p)], by rw [x4, h.2.2.1], by rw [x5, (X.S p)], x6, by rw [x7, (X.S p)]⟩
  have cargs : ∀ {ac : State × Nat} {t : State}, U₂ ac t →
      ∃ s, Pre s ∧ UpdArgs S vf G s t (off (S s) oCtr) 4 ∧ Pub ac.1 s := fun {ac t} h => by
    obtain ⟨hm, h3, -, h5, h6, h7⟩ := h
    obtain ⟨s, P, p, b⟩ := hm.1
    exact ⟨s, P, ⟨X.fits P, b, by rw [h3, (X.S p)], by rw [h5, (X.S p)], by rw [h6]; rfl, by rw [h7, (X.S p)],
      Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) (by omega_arith)),
      sdis (.inr (by omega_arith)) (by omega_arith) (by omega_arith), sdis (.inl (by omega_arith)) (by omega_arith) (by omega_arith),
      cR_dis (X.fits P) (by omega_arith)⟩, p⟩
  refine two_seq (Ψ := M) (upd_ct (S := S) (vf := vf) cG fun t₁ t₂ ⟨ac, h₁, h₂⟩ => ?_) (fun ac t h => ?_) ?_
  · obtain ⟨s₁, -, A₁, p₁⟩ := cargs h₁
    obtain ⟨s₂, -, A₂, p₂⟩ := cargs h₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm, h₁.2.2.2.2.2.trans h₂.2.2.2.2.2.symm]
  · obtain ⟨s, P, A, p⟩ := cargs h
    exact WP.mono (upd_ok A.P hG A.b A.h3 A.h5 A.h6 A.h7 A.hdc A.hd₁ A.hd₂ A.hd₃) fun t' ⟨b', g', _⟩ =>
      h.1.keep ⟨s, P, p, b'⟩ (pres g')
  -- `finalize`.
  let U₃ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .r3 = off (S ac.1) oSt ∧
    t.gpr .r4 = BitVec.ofNat 64 srcLen + BitVec.ofNat 64 4 ∧ t.gpr .r5 = off (S ac.1) oDig ∧
    t.gpr .r6 = off (S ac.1) oW
  refine two_seq (Ψ := U₃) (r4_taint (p0 fun _ _ h => h)) (fun ac t h => ?_) ?_
  · refine wp_addi fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ => wp_addi fun t₃ o₃ e₃ => wp_addi fun t₄ o₄ e₄ =>
      wp_nil ?_
    have k : Only [.r3, .r4, .r5, .r6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    obtain ⟨s, P, p, b⟩ := h.1
    refine ⟨h.keep (h.1.onlyS X k) (fun r hr => k.gpr r (by revert r; decide)), ?_, ?_, ?_, ?_⟩
    · rw [o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, b.r14, (X.S p)]
    · rw [o₄.get .r4, o₃.get .r4, e₂, o₁.get .r25, h.2.2.1]
    · rw [o₄.get .r5, e₃, o₂.get .r14, o₁.get .r14, b.r14, (X.S p)]
    · rw [e₄, o₃.get .r14, o₂.get .r14, o₁.get .r14, b.r14, (X.S p)]
  refine two_seq (Ψ := M) (fin_ct (S := S) (vf := vf) cG fun t₁ t₂ ⟨ac, h₁, h₂⟩ => ?_) (fun ac t h => ?_) ?_
  · obtain ⟨⟨⟨s₁, P₁, p₁, b₁⟩, _⟩, x3, x4, x5, x6⟩ := h₁
    obtain ⟨⟨⟨s₂, P₂, p₂, b₂⟩, _⟩, y3, y4, y5, y6⟩ := h₂
    refine ⟨s₁, s₂, ⟨X.fits P₁, b₁, by rw [x3, (X.S p₁)], by rw [x5, (X.S p₁)], by rw [x6, (X.S p₁)]⟩,
      ⟨X.fits P₂, b₂, by rw [y3, (X.S p₂)], by rw [y5, (X.S p₂)], by rw [y6, (X.S p₂)]⟩, fun r hr => ?_,
      (Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [x3.trans y3.symm, x4.trans y4.symm, x5.trans y5.symm, x6.trans y6.symm]
  · obtain ⟨hm, h3, -, h5, h6⟩ := h
    obtain ⟨s, P, p, b⟩ := hm.1
    exact WP.mono (fin_ok (X.fits P) hG b (by rw [h3, (X.S p)]) (by rw [h5, (X.S p)]) (by rw [h6, (X.S p)])) fun t' ⟨b', g', _⟩ =>
      hm.keep ⟨s, P, p, b'⟩ (pres g')
  -- Into `dst`, and the next counter.
  exact two_seq (Ψ := fun ac t => B S vf Pre Pub ac.1 t) (xorOut_taint G (pins_mono (mgfR_pins X fun _ _ h => h)))
    (fun ac t h => xorOut_base X hG hf h)
    (nextCtr_taint G fun ac t₁ t₂ h₁ h₂ => ⟨(h₁.spS X).trans (h₂.spS X).symm, fun _ h => nomatch h⟩)

/-- MGF1's arguments in `r24`–`r27`, from the anchor. -/
def MgfA (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  ∃ s, Pre s ∧ Pub a s ∧ Base S vf s t ∧ t.gpr .r24 = off (S a) src ∧
    t.gpr .r25 = BitVec.ofNat 64 srcLen ∧ t.gpr .r26 = off (S a) dst ∧
    t.gpr .r27 = BitVec.ofNat 64 dstLen

variable {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs)

/-- After `c` rounds, in a run: `MgfI` for some view, and the counter below
the end. -/
def MgfL (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (G : Hash) (Gs : Spec.Mgf1.Hash) (src srcLen dst dstLen : Nat) (ac : State × Nat) (t : State) : Prop :=
  ∃ s V, Pre s ∧ Pub ac.1 s ∧
    MgfI S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D ac.2 t ∧ ac.2 * G.D < dstLen

include X in
theorem mgfL_r {ac : State × Nat} {t : State} (h : MgfL S vf Pre Pub G Gs src srcLen dst dstLen ac t) :
    MgfR S vf Pre Pub G.D src srcLen dst dstLen ac t := by
  obtain ⟨s, V, P, p, I, hc⟩ := h
  exact ⟨⟨s, P, p, I.base⟩, by rw [I.r24, (X.S p)], I.r25, by rw [I.r26, (X.S p)], I.r27, I.r28, I.r29, hc⟩

include X cG hf hGh hGl hGv in
theorem mgfXor_ctS : RelCT isa (Two (MgfA S vf Pre Pub src srcLen dst dstLen)) (mgfXor G) fun _ _ => True := by
  have hD0 := hG.hD0
  have hpos := hf.pos
  let L := MgfL S vf Pre Pub G Gs src srcLen dst dstLen
  let Ln := fun (n : Nat) (ac : State × Nat) (t : State) => L ac t ∧ n = dstLen - ac.2 * G.D
  have step : ∀ n, RelCT isa (Two (Ln n)) (round G) fun s₁ s₂ =>
      isa.eval (.nonzero .d .r12) s₁ = isa.eval (.nonzero .d .r12) s₂ ∧
      (isa.eval (.nonzero .d .r12) s₁ = some false → True) ∧
      (isa.eval (.nonzero .d .r12) s₁ = some true → ∃ m < n, Two (Ln m) s₁ s₂) := fun n => by
    have h := two_post (Φ := Ln n) (Ψ := fun ac t => (t.gpr .r12 != 0) = decide ((ac.2 + 1) * G.D < dstLen) ∧
        ∃ s V, Pre s ∧ Pub ac.1 s ∧
          MgfI S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D (ac.2 + 1) t ∧
          n = dstLen - ac.2 * G.D)
      ((round_ct X hG cG hf).mono (fun _ _ ⟨ac, h₁, h₂⟩ => ⟨ac, mgfL_r X h₁.1, mgfL_r X h₂.1⟩) fun _ _ h => h)
      (fun ac t ⟨⟨s, V, P, p, I, hc⟩, hn⟩ => WP.mono (round_ok (X.fits P) hG hGh hGl hGv hf I hc)
        fun t' ⟨hcf, I'⟩ => ⟨hcf, s, V, P, p, I', hn⟩)
    refine h.mono (fun _ _ h => h) fun s₁ s₂ ⟨ac, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ => ?_
    have hs1 : (ac.2 + 1) * G.D = ac.2 * G.D + G.D := Nat.succ_mul _ _
    refine ⟨by rw [eval_nonzero, eval_nonzero, c₁, c₂], fun _ => trivial, fun ht => ?_⟩
    rw [eval_nonzero, c₁] at ht
    have hlt : (ac.2 + 1) * G.D < dstLen := by simpa using ht
    obtain ⟨s, V, P, p, I, hn⟩ := h₁
    obtain ⟨s', V', P', p', I', -⟩ := h₂
    exact ⟨dstLen - (ac.2 + 1) * G.D, by omega_arith, (ac.1, ac.2 + 1), ⟨⟨s, V, P, p, I, hlt⟩, rfl⟩,
      ⟨⟨s', V', P', p', I', hlt⟩, rfl⟩⟩
  refine RelCT.seq (two_post (Ψ := fun a t => L (a, 0) t) (mgfHead_taint fun a t₁ t₂ h₁ h₂ => ?_)
    (fun a t h => ?_)) ((RelCT.loop (fun n => Two (Ln n)) step (dstLen - 0 * G.D)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩) fun _ _ h => h)
  · obtain ⟨_, -, p₁, b₁, -⟩ := h₁
    obtain ⟨_, -, p₂, b₂, -⟩ := h₂
    exact ⟨(Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm, fun _ h => nomatch h⟩
  · obtain ⟨s, P, p, b, h24, h25, h26, h27⟩ := h
    refine wp_li (by decide) fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_nil ?_
    have k₂ : Only [.r28, .r29] t t₂ := (o₁.trans o₂).mono
    exact ⟨s, view t.mem (S s), P, p, ⟨b.only (X.fits P) k₂, by rw [k₂.get .r24, h24, (X.S p)], by rw [k₂.get .r25, h25],
      by rw [k₂.get .r26, h26, (X.S p)], by rw [k₂.get .r27, h27], by rw [o₂.get .r28, e₁], by rw [e₂, Nat.zero_mul],
      fun o _ => by rw [mixV, ifn (by omega_arith), k₂.mem]⟩, by omega_arith⟩

end

/-- `mgfXor_ctS` for `Ok`. -/
theorem mgfXor_ct {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop}
    {Pub : State → State → Prop} (X : Ok S vf Pre Pub) {G : Hash} (hG : HashOK G) (cG : HashCT hG)
    {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) :
    RelCT isa (Two (MgfA S vf Pre Pub src srcLen dst dstLen)) (mgfXor G) fun _ _ => True :=
  mgfXor_ctS X.s hG cG hf hGh hGl hGv

end VG.Proof.RsaOaep.PPC64LE
