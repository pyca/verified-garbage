module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBase
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Mgf
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# MGF1 on RISC-V, through its hash function's own calls: constant time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/CTMgf.lean`), for RSASSA-PSS, which calls MGF1's
hash function by name. `round_ct`: two runs of a round of `mgfXor` from
states with `B` and the same MGF1 registers (`MgfR`) leak alike;
`mgfXor_ct`: the loop, whose condition both runs agree on since each
satisfies `MgfI` for the same counter (`round_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo Two Pins two_post two_ite wp_li wp_addi wp_subi
  wp_mov wp_sub wp_srl wp_or wp_nil eval_nonzero)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

/-- In a round: `B` and MGF1's registers, for the counter `c`. -/
def MgfR (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (Dg src srcLen dst dstLen : Nat) (ac : State × Nat) (t : State) : Prop :=
  B S vf Pre Pub ac.1 t ∧ t.gpr .s6 = off (S ac.1) src ∧ t.gpr .s7 = BitVec.ofNat 64 srcLen ∧
    t.gpr .s8 = off (S ac.1) dst ∧ t.gpr .s9 = BitVec.ofNat 64 dstLen ∧
    t.gpr .s10 = BitVec.ofNat 64 ac.2 ∧ t.gpr .s11 = BitVec.ofNat 64 (ac.2 * Dg) ∧ ac.2 * Dg < dstLen

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  {Dg src srcLen dst dstLen : Nat}

theorem MgfR.keep {ac : State × Nat} {t t' : State} (h : MgfR S vf Pre Pub Dg src srcLen dst dstLen ac t)
    (hb : B S vf Pre Pub ac.1 t') (hg : ∀ r ∈ [Reg.s6, .s7, .s8, .s9, .s10, .s11], t'.gpr r = t.gpr r) :
    MgfR S vf Pre Pub Dg src srcLen dst dstLen ac t' :=
  ⟨hb, (hg _ (by decide)).trans h.2.1, (hg _ (by decide)).trans h.2.2.1, (hg _ (by decide)).trans h.2.2.2.1,
    (hg _ (by decide)).trans h.2.2.2.2.1, (hg _ (by decide)).trans h.2.2.2.2.2.1,
    (hg _ (by decide)).trans h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem mgfR_pins (X : OkS S Pre Pub) {Φ : State × Nat → State → Prop}
    (h : ∀ ac t, Φ ac t → MgfR S vf Pre Pub Dg src srcLen dst dstLen ac t) :
    Pins Φ [.s0, .s8, .s9, .s11] := fun ac t₁ t₂ h₁ h₂ => by
  obtain ⟨b₁, -, -, x8, x9, -, x11, -⟩ := h ac t₁ h₁
  obtain ⟨b₂, -, -, y8, y9, -, y11, -⟩ := h ac t₂ h₂
  refine ⟨(b₁.spS X).trans (b₂.spS X).symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (b₁.s0S X).trans (b₂.s0S X).symm
  exacts [x8.trans y8.symm, x9.trans y9.symm, x11.trans y11.symm]

theorem pins_mono {α : Type} {Φ : α → State → Prop} {rs rs' : List Reg} (h : Pins Φ rs)
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : Pins Φ rs' := fun a t₁ t₂ h₁ h₂ =>
  ⟨(h a t₁ t₂ h₁ h₂).1, fun r hr => (h a t₁ t₂ h₁ h₂).2 r (hs r hr)⟩

end

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : OkS S Pre Pub) {G : Hash} (hG : HashOK G) (cG : HashCT hG) (hF : G.F ≤ 208) {src srcLen dst dstLen : Nat}
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
  obtain ⟨_, _, _, _, _⟩ := offs
  have hD0 := hG.hD0
  have hD64 := hG.hD64
  have hfd := hf.fd
  obtain ⟨⟨s, P, p, b⟩, -, -, h8, h9, -, h11, hc⟩ := h
  have hdc := Nat.min_le_left G.D (dstLen - ac.2 * G.D)
  have hn0 : 0 < min G.D (dstLen - ac.2 * G.D) := by omega
  refine WP.seq (WP.mono (xorHead_ok (G := G) (S := S s) (dst := dst) (dstLen := dstLen) (done := ac.2 * G.D)
    (by omega) b.s0 (by rw [h8, (X.S p)]) h9 h11 hc (by omega)) fun t₁ ⟨k₁, x4, x5, x6⟩ => ?_)
  have b₁ := b.only (X.fits P) k₁
  refine WP.mono (xorLoop_ok (p := off (S s) (dst + ac.2 * G.D)) (q := off (S s) oDig) hn0 (by omega) x4 x5 x6
    (fun j hj => by
      rw [off_add, k₁.rd, k₁.wr, b.wr, b.rd]; exact sc_inR (X.fits P) (by omega) _)
    (sc_w (X.fits P) (by rw [k₁.wr, b.wr]) (by omega))
    (fun j hj i hi => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))
    (fun i hi j hj hij => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)))
    fun t₂ ⟨k₂, x₂⟩ => ⟨s, P, p, b₁.wb (X.fits P) k₂ (by rw [xorAt_length]; omega) x₂⟩

include X cG hF hf in
theorem round_ct :
    RelCT isa (Two (MgfR S vf Pre Pub G.D src srcLen dst dstLen)) (round G) fun _ _ => True := by
  have F := hfits hG
  obtain ⟨_, _, _, _, _⟩ := offs
  have hfs := hf.fs
  have hfd := hf.fd
  have p0 : ∀ {Φ : State × Nat → State → Prop},
      (∀ ac t, Φ ac t → MgfR S vf Pre Pub G.D src srcLen dst dstLen ac t) → Pins Φ [] :=
    fun h ac t₁ t₂ h₁ h₂ => ⟨((mgfR_pins X h) ac t₁ t₂ h₁ h₂).1, fun _ h => nomatch h⟩
  let M := MgfR S vf Pre Pub G.D src srcLen dst dstLen
  have pres : ∀ {t t' : State}, (∀ r ∈ preserved, t'.gpr r = t.gpr r) →
      ∀ r ∈ [Reg.s6, .s7, .s8, .s9, .s10, .s11], t'.gpr r = t.gpr r :=
    fun h r hr => h r (by revert r; decide)
  -- `init`.
  refine two_seq (Ψ := fun ac t => M ac t ∧ t.gpr .a0 = off (S ac.1) oSt) (st_taint (p0 fun _ _ h => h))
    (fun ac t h => wp_addi (imm := oSt) fun t' o e => wp_nil ⟨h.keep (h.1.onlyS X o)
      (fun r hr => o.gpr r (by revert r; decide)),
      by obtain ⟨⟨s, _, p, b⟩, _⟩ := h; rw [e, b.s0, (X.S p)]⟩) ?_
  refine two_seq (Ψ := M) (init_ct (S := S) (vf := vf) cG fun t₁ t₂ hp => ?_) (fun ac t h => ?_) ?_
  · obtain ⟨ac, s₁, s₂, h₁, h₂, P₁, p₁, b₁, P₂, p₂, b₂⟩ := two_args hp fun ac t h => h.1.1
    exact ⟨s₁, s₂, X.fits P₁, b₁, by rw [h₁.2, (X.S p₁)], X.fits P₂, b₂, by rw [h₂.2, (X.S p₂)],
      h₁.2.trans h₂.2.symm, (Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm⟩
  · obtain ⟨hm, h0⟩ := h
    obtain ⟨s, P, p, b⟩ := hm.1
    exact WP.mono (init_ok (X.fits P) hG hF b (by rw [h0, (X.S p)])) fun t' ⟨b', g', _⟩ =>
      hm.keep ⟨s, P, p, b'⟩ (pres g')
  -- `update` with `src`.
  let U₁ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .a0 = off (S ac.1) oSt ∧
    t.gpr .a1 = 0 ∧ t.gpr .a2 = off (S ac.1) src ∧ t.gpr .a3 = BitVec.ofNat 64 srcLen
  refine two_seq (Ψ := U₁) (upd1_taint (p0 fun _ _ h => h)) (fun ac t h => ?_) ?_
  · refine wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_li (imm := 0) (by decide) fun t₂ o₂ e₂ =>
      wp_mov fun t₃ o₃ e₃ => wp_mov fun t₄ o₄ e₄ => wp_nil ?_
    have k : Only [.a0, .a1, .a2, .a3] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    obtain ⟨s, P, p, b⟩ := h.1
    refine ⟨h.keep (h.1.onlyS X k) (fun r hr => k.gpr r (by revert r; decide)), ?_, ?_, ?_, ?_⟩
    · rw [o₄.get .a0, o₃.get .a0, o₂.get .a0, e₁, b.s0, (X.S p)]
    · rw [o₄.get .a1, o₃.get .a1, e₂]; rfl
    · rw [o₄.get .a2, e₃, o₂.get .s6, o₁.get .s6, h.2.1]
    · rw [e₄, o₃.get .s7, o₂.get .s7, o₁.get .s7, h.2.2.1]
  have uargs : ∀ {ac : State × Nat} {t : State}, U₁ ac t →
      ∃ s, Pre s ∧ UpdArgs S vf G s t (off (S s) src) srcLen ∧ Pub ac.1 s := fun {ac t} h => by
    obtain ⟨hm, h0, -, h2, h3⟩ := h
    obtain ⟨s, P, p, b⟩ := hm.1
    exact ⟨s, P, ⟨X.fits P, b, by rw [h0, (X.S p)], by rw [h2, (X.S p)],
      by rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
      Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) (by omega)),
      sdis (.inl (by omega)) (by omega) (by omega), cR_dis (X.fits P) (by omega)⟩, p⟩
  refine two_seq (Ψ := M) (upd_ct (S := S) (vf := vf) cG hF fun t₁ t₂ ⟨ac, h₁, h₂⟩ => ?_)
    (fun ac t h => ?_) ?_
  · obtain ⟨s₁, -, A₁, p₁⟩ := uargs h₁
    obtain ⟨s₂, -, A₂, p₂⟩ := uargs h₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.trans h₂.2.2.2.2.symm]
  · obtain ⟨s, P, A, p⟩ := uargs h
    exact WP.mono (upd_ok A.P hG hF A.b A.h0 A.h2 A.h3 A.hdc A.hd₁ A.hd₃) fun t' ⟨b', g', _⟩ =>
      h.1.keep ⟨s, P, p, b'⟩ (pres g')
  -- The counter, and `update` with it.
  let U₂ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .a0 = off (S ac.1) oSt ∧
    t.gpr .a1 = BitVec.ofNat 64 srcLen ∧ t.gpr .a2 = off (S ac.1) oCtr ∧ t.gpr .a3 = BitVec.ofNat 64 4
  have hD0 := hG.hD0
  refine two_seq (Ψ := U₂) (ctr_taint (pins_mono (mgfR_pins X fun _ _ h => h))) (fun ac t h => ?_) ?_
  · obtain ⟨s, P, p, b⟩ := h.1
    have hc : ac.2 < 2 ^ 32 := by
      have := h.2.2.2.2.2.2.2; have := Nat.le_mul_of_pos_right ac.2 hD0; omega
    exact WP.mono (ctr_ok (X.fits P) b h.2.2.2.2.2.1 hc) fun t' ⟨b', g', _, x0, x1, x2, x3⟩ =>
      ⟨h.keep ⟨s, P, p, b'⟩ (pres g'), by rw [x0, (X.S p)], by rw [x1, h.2.2.1], by rw [x2, (X.S p)], x3⟩
  have cargs : ∀ {ac : State × Nat} {t : State}, U₂ ac t →
      ∃ s, Pre s ∧ UpdArgs S vf G s t (off (S s) oCtr) 4 ∧ Pub ac.1 s := fun {ac t} h => by
    obtain ⟨hm, h0, -, h2, h3⟩ := h
    obtain ⟨s, P, p, b⟩ := hm.1
    exact ⟨s, P, ⟨X.fits P, b, by rw [h0, (X.S p)], by rw [h2, (X.S p)], by rw [h3]; rfl,
      Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) (by omega)),
      sdis (.inr (by omega)) (by omega) (by omega), cR_dis (X.fits P) (by omega)⟩, p⟩
  refine two_seq (Ψ := M) (upd_ct (S := S) (vf := vf) cG hF fun t₁ t₂ ⟨ac, h₁, h₂⟩ => ?_)
    (fun ac t h => ?_) ?_
  · obtain ⟨s₁, -, A₁, p₁⟩ := cargs h₁
    obtain ⟨s₂, -, A₂, p₂⟩ := cargs h₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.trans h₂.2.2.2.2.symm]
  · obtain ⟨s, P, A, p⟩ := cargs h
    exact WP.mono (upd_ok A.P hG hF A.b A.h0 A.h2 A.h3 A.hdc A.hd₁ A.hd₃) fun t' ⟨b', g', _⟩ =>
      h.1.keep ⟨s, P, p, b'⟩ (pres g')
  -- `finalize`.
  let U₃ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .a0 = off (S ac.1) oSt ∧
    t.gpr .a1 = BitVec.ofNat 64 srcLen + BitVec.ofNat 64 4 ∧ t.gpr .a2 = off (S ac.1) oDig
  refine two_seq (Ψ := U₃) (r4_taint (p0 fun _ _ h => h)) (fun ac t h => ?_) ?_
  · refine wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_addi (imm := 4) fun t₂ o₂ e₂ =>
      wp_addi (imm := oDig) fun t₃ o₃ e₃ => wp_nil ?_
    have k : Only [.a0, .a1, .a2] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    obtain ⟨s, P, p, b⟩ := h.1
    refine ⟨h.keep (h.1.onlyS X k) (fun r hr => k.gpr r (by revert r; decide)), ?_, ?_, ?_⟩
    · rw [o₃.get .a0, o₂.get .a0, e₁, b.s0, (X.S p)]
    · rw [o₃.get .a1, e₂, o₁.get .s7, h.2.2.1]
    · rw [e₃, o₂.get .s0, o₁.get .s0, b.s0, (X.S p)]
  refine two_seq (Ψ := M) (fin_ct (S := S) (vf := vf) cG hF fun t₁ t₂ ⟨ac, h₁, h₂⟩ => ?_)
    (fun ac t h => ?_) ?_
  · obtain ⟨⟨⟨s₁, P₁, p₁, b₁⟩, _⟩, x0, x1, x2⟩ := h₁
    obtain ⟨⟨⟨s₂, P₂, p₂, b₂⟩, _⟩, y0, y1, y2⟩ := h₂
    refine ⟨s₁, s₂, ⟨X.fits P₁, b₁, by rw [x0, (X.S p₁)], by rw [x2, (X.S p₁)]⟩,
      ⟨X.fits P₂, b₂, by rw [y0, (X.S p₂)], by rw [y2, (X.S p₂)]⟩, fun r hr => ?_,
      (Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [x0.trans y0.symm, x1.trans y1.symm, x2.trans y2.symm]
  · obtain ⟨hm, h0, -, h2⟩ := h
    obtain ⟨s, P, p, b⟩ := hm.1
    exact WP.mono (fin_ok (X.fits P) hG hF b (by rw [h0, (X.S p)]) (by rw [h2, (X.S p)]))
      fun t' ⟨b', g', _⟩ => hm.keep ⟨s, P, p, b'⟩ (pres g')
  -- Into `dst`, and the next counter.
  exact two_seq (Ψ := fun ac t => B S vf Pre Pub ac.1 t) (xorOut_taint G (pins_mono (mgfR_pins X fun _ _ h => h)))
    (fun ac t h => xorOut_base X hG hf h)
    (nextCtr_taint G fun ac t₁ t₂ h₁ h₂ => ⟨(h₁.spS X).trans (h₂.spS X).symm, fun _ h => nomatch h⟩)

/-- MGF1's arguments in `s6`–`s9`, from the anchor. -/
def MgfA (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  ∃ s, Pre s ∧ Pub a s ∧ Base S vf s t ∧ t.gpr .s6 = off (S a) src ∧
    t.gpr .s7 = BitVec.ofNat 64 srcLen ∧ t.gpr .s8 = off (S a) dst ∧
    t.gpr .s9 = BitVec.ofNat 64 dstLen

variable {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs)

/-- After `c` rounds, in a run: `MgfI` for some view, and the counter below
the end. -/
def MgfL (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (G : Hash) (Gs : Spec.Mgf1.Hash) (src srcLen dst dstLen : Nat) (ac : State × Nat) (t : State) : Prop :=
  ∃ s V, Pre s ∧ Pub ac.1 s ∧
    MgfI S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D ac.2 t ∧
      ac.2 * G.D < dstLen

include X in
theorem mgfL_r {ac : State × Nat} {t : State} (h : MgfL S vf Pre Pub G Gs src srcLen dst dstLen ac t) :
    MgfR S vf Pre Pub G.D src srcLen dst dstLen ac t := by
  obtain ⟨s, V, P, p, I, hc⟩ := h
  exact ⟨⟨s, P, p, I.base⟩, by rw [I.s6, (X.S p)], I.s7, by rw [I.s8, (X.S p)], I.s9, I.s10, I.s11, hc⟩

include X cG hF hf hGh hGl hGv in
theorem mgfXor_ctS : RelCT isa (Two (MgfA S vf Pre Pub src srcLen dst dstLen)) (mgfXor G) fun _ _ => True := by
  have hD0 := hG.hD0
  have hpos := hf.pos
  let L := MgfL S vf Pre Pub G Gs src srcLen dst dstLen
  let Ln := fun (n : Nat) (ac : State × Nat) (t : State) => L ac t ∧ n = dstLen - ac.2 * G.D
  have step : ∀ n, RelCT isa (Two (Ln n)) (round G) fun s₁ s₂ =>
      isa.eval (.nonzero .t1) s₁ = isa.eval (.nonzero .t1) s₂ ∧
      (isa.eval (.nonzero .t1) s₁ = some false → True) ∧
      (isa.eval (.nonzero .t1) s₁ = some true → ∃ m < n, Two (Ln m) s₁ s₂) := fun n => by
    have h := two_post (Φ := Ln n) (Ψ := fun ac t => (t.gpr .t1 != 0) = decide ((ac.2 + 1) * G.D < dstLen) ∧
        ∃ s V, Pre s ∧ Pub ac.1 s ∧
          MgfI S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D (ac.2 + 1) t ∧
          n = dstLen - ac.2 * G.D)
      ((round_ct X hG cG hF hf).mono (fun _ _ ⟨ac, h₁, h₂⟩ => ⟨ac, mgfL_r X h₁.1, mgfL_r X h₂.1⟩)
        fun _ _ h => h)
      (fun ac t ⟨⟨s, V, P, p, I, hc⟩, hn⟩ => WP.mono (round_ok (X.fits P) hG hF hGh hGl hGv hf I hc)
        fun t' ⟨hcf, I'⟩ => ⟨hcf, s, V, P, p, I', hn⟩)
    refine h.mono (fun _ _ h => h) fun s₁ s₂ ⟨ac, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ => ?_
    refine ⟨by rw [eval_nonzero, eval_nonzero, c₁, c₂], fun _ => trivial, fun ht => ?_⟩
    rw [eval_nonzero, c₁] at ht
    have hlt : (ac.2 + 1) * G.D < dstLen := by simpa using ht
    have hs1 : (ac.2 + 1) * G.D = ac.2 * G.D + G.D := Nat.succ_mul _ _
    obtain ⟨s, V, P, p, I, hn⟩ := h₁
    obtain ⟨s', V', P', p', I', -⟩ := h₂
    exact ⟨dstLen - (ac.2 + 1) * G.D, by omega, (ac.1, ac.2 + 1), ⟨⟨s, V, P, p, I, hlt⟩, rfl⟩,
      ⟨⟨s', V', P', p', I', hlt⟩, rfl⟩⟩
  refine RelCT.seq (two_post (Ψ := fun a t => L (a, 0) t) (mgfHead_taint fun a t₁ t₂ h₁ h₂ => ?_)
    (fun a t h => ?_)) ((RelCT.loop (fun n => Two (Ln n)) step (dstLen - 0 * G.D)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩) fun _ _ h => h)
  · obtain ⟨_, -, p₁, b₁, -⟩ := h₁
    obtain ⟨_, -, p₂, b₂, -⟩ := h₂
    exact ⟨(Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm, fun _ h => nomatch h⟩
  · obtain ⟨s, P, p, b, h6, h7, h8, h9⟩ := h
    refine wp_li (imm := 0) (by decide) fun t₁ o₁ e₁ => wp_li (imm := 0) (by decide) fun t₂ o₂ e₂ => wp_nil ?_
    have k₂ : Only [.s10, .s11] t t₂ := (o₁.trans o₂).mono
    exact ⟨s, view t.mem (S s), P, p, ⟨b.only (X.fits P) k₂, by rw [k₂.get .s6, h6, (X.S p)],
      by rw [k₂.get .s7, h7], by rw [k₂.get .s8, h8, (X.S p)], by rw [k₂.get .s9, h9],
      by rw [o₂.get .s10, e₁], by rw [e₂, Nat.zero_mul],
      fun o _ => by rw [mixV, ifn (by omega), k₂.mem]⟩, by omega⟩

end

/-- `mgfXor_ctS` for `Ok`. -/
theorem mgfXor_ct {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop}
    {Pub : State → State → Prop} (X : Ok S vf Pre Pub) {G : Hash} (hG : HashOK G) (cG : HashCT hG)
    (hF : G.F ≤ 208) {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) :
    RelCT isa (Two (MgfA S vf Pre Pub src srcLen dst dstLen)) (mgfXor G) fun _ _ => True :=
  mgfXor_ctS X.s hG cG hF hf hGh hGl hGv


end VG.Proof.RsaOaep.RISCV64
