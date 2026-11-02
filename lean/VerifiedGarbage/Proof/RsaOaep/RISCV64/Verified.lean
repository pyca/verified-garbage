module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBase
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Correct
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Mgf
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Pre
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Pub
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Em
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Label
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Main
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP encryption on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Verified.lean`, `Hashes.lean`, `Inst.lean`): the
shared contract's public data as `PubO` (`pubO_of`); constant time
(`code_constantTime`, from `code_ct`); states meeting the precondition for
the hash functions the label is hashed with (`enc_sat`); `enc_verified`.
The streaming functions of SHA-1 and the SHA-2 family
(`Proof/Hmac/Stream/RISCV64/`) are constant time for the contracts the proofs
call them by (`HashCT`), from their artifacts' proofs; with what the proofs
need of them (`Link`), `link_verified` is encryption for two of them, which
the registration files bind.
-/

@[expose] public section

/-!
# RSAES-OAEP encryption on RISC-V: constant time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/CTLabel.lean`, `CTMgf.lean`, `CTMain.lean`). Two
runs are compared through an anchor `a`, a state with their public data
(`PubO`): the pointers and lengths, `e`'s bytes and the precomputed values;
`BO D a t`: `t` has `Base` from an entry state with `a`'s public data.
`hashLabel_ct`: the label's hash (with the label's pointer and length in
`s6` and `s7`, `LabB`). `round_ct`: two runs of a round of `mgfXor` from
states with `Base` and the same MGF1 registers (`MgfR`) leak alike;
`mgfXor_ct`: the loop, whose condition both runs agree on since each
satisfies `MgfI` for the same counter (`round_ok`). `code_ct`: the code
between the calls by the taint analysis (`CTBlocks`), the hash functions'
calls by their contracts (`init_ct`, `upd_ct`, `fin_ct`), the call of
`vg_rsa_public_precomputed_checked` by its contract (`pdCallCT`), and the
branches on the public lengths (`two_ite`); what each run satisfies between
them follows from correctness.
-/


namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi
  wp_mov wp_sub wp_srl wp_or wp_nil eval_nonzero pdCallCT)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s. -/
structure PubO (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], s.gpr r = a.gpr r
  args : ∀ i < 7, stackArg s i = stackArg a i
  e : Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a4) (a.gpr .a5).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat

theorem PubO.S {a s : State} (p : PubO a s) : S s = stackArg a 3 := p.args 3 (by decide)

/-- `PubO` gives what the shared code needs. -/
theorem oaepOk (D : Nat) : Ok S vO (PreO D) PubO where
  fits P := P.fits
  agree {a s} p := ⟨p.sp, p.S, fun r hr => by
    simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [vO] <;> exact p.g _ (by decide)⟩

/-- `t` has `Base` from an entry state with `a`'s public data. -/
abbrev BO (D : Nat) : State → State → Prop := B S vO (PreO D) PubO

/-! ## The label's hash -/

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208)

/-- `BO`, with the label's pointer and length in `s6` and `s7`. -/
def LabB (H : Hash) (a t : State) : Prop := BO H.D a t ∧ t.gpr .s6 = a.gpr .a6 ∧ t.gpr .s7 = a.gpr .a7

/-- The label's update: its arguments. -/
def LabU (H : Hash) (a t : State) : Prop :=
  LabB H a t ∧ t.gpr .a0 = off (stackArg a 3) oSt ∧ t.gpr .a1 = 0 ∧ t.gpr .a2 = a.gpr .a6 ∧
    t.gpr .a3 = a.gpr .a7

/-- The label's finalize: its arguments. -/
def LabF (H : Hash) (a t : State) : Prop :=
  BO H.D a t ∧ t.gpr .a0 = off (stackArg a 3) oSt ∧ t.gpr .a1 = a.gpr .a7 ∧ t.gpr .a2 = off (stackArg a 3) oDig

theorem LabB.keep {a t t' : State} (h : LabB H a t) (hb : BO H.D a t') (h6 : t'.gpr .s6 = t.gpr .s6)
    (h7 : t'.gpr .s7 = t.gpr .s7) : LabB H a t' := ⟨hb, h6.trans h.2.1, h7.trans h.2.2⟩

include hH in
theorem lab_args {a t : State} (h : LabU H a t) :
    ∃ s, PreO H.D s ∧ UpdArgs S vO H s t (s.gpr .a6) (s.gpr .a7).toNat ∧ PubO a s := by
  obtain ⟨⟨⟨s, P, p, b⟩, -, -⟩, h0, -, h2, h3⟩ := h
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  have hl : lR s ∈ s.rd := by rw [P.hrd]; simp
  have hc : Covers [lR s] (t.rd ++ t.wr) :=
    Covers.left (by rw [b.rd]; exact Covers.of_mem fun r hr => (List.mem_singleton.mp hr) ▸ hl)
  refine ⟨s, P, ⟨P.fits, b, by rw [h0, p.S], by rw [h2, p.g _ (by decide)], by rw [h3, p.g _ (by decide)],
    hc, (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)), P.kl.sub_left (cR_sub s)⟩, p⟩

include hH cH hF in
theorem hashLabel_ct : RelCT isa (Two (LabB H)) (hashLabel H) fun _ _ => True := by
  have X := oaepOk H.D
  refine two_seq (Ψ := fun a t => LabB H a t ∧ t.gpr .a0 = off (S a) oSt)
    (st_taint (pins_of X (fun _ _ h => h.1) [])) (fun a t h => ?_) ?_
  · exact wp_addi (imm := oSt) fun t' o e => wp_nil ⟨h.keep (h.1.only X o) (o.get .s6) (o.get .s7),
      by rw [e, (h.1.agree X).2.1]⟩
  refine two_seq (Ψ := LabB H) (init_two X hH cH fun _ _ h => ⟨h.1.1, h.2⟩) (fun a t h => ?_) ?_
  · obtain ⟨⟨⟨s, P, p, b⟩, h6, h7⟩, h0⟩ := h
    exact WP.mono (init_ok P.fits hH hF b (by rw [h0, p.S])) fun t' ⟨b', g', _⟩ =>
      ⟨⟨s, P, p, b'⟩, (g' .s6 (by decide)).trans h6, (g' .s7 (by decide)).trans h7⟩
  refine two_seq (Ψ := LabU H) (upd1_taint (pins_of X (fun _ _ h => h.1) [])) (fun a t h => ?_) ?_
  · obtain ⟨⟨s, P, p, b⟩, h6, h7⟩ := h
    refine wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_li (imm := 0) (by decide) fun t₂ o₂ e₂ =>
      wp_mov fun t₃ o₃ e₃ => wp_mov fun t₄ o₄ e₄ => wp_nil ?_
    have k : Only [.a0, .a1, .a2, .a3] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    refine ⟨⟨⟨s, P, p, b.only P.fits k⟩, by rw [k.get .s6, h6], by rw [k.get .s7, h7]⟩, ?_, ?_, ?_, ?_⟩
    · rw [o₄.get .a0, o₃.get .a0, o₂.get .a0, e₁, b.s0, p.S]
    · rw [o₄.get .a1, o₃.get .a1, e₂]; rfl
    · rw [o₄.get .a2, e₃, o₂.get .s6, o₁.get .s6, h6]
    · rw [e₄, o₃.get .s7, o₂.get .s7, o₁.get .s7, h7]
  refine two_seq (Ψ := LabB H) (upd_ct (S := S) (vf := vO) cH hF fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_)
    (fun a t h => ?_) ?_
  · obtain ⟨s₁, -, A₁, p₁⟩ := lab_args hH h₁
    obtain ⟨s₂, -, A₂, p₂⟩ := lab_args hH h₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_,
      (A₁.b.agree (X.agree p₁)).1.trans (A₂.b.agree (X.agree p₂)).1.symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.trans h₂.2.2.2.2.symm]
  · obtain ⟨s, P, A, p⟩ := lab_args hH h
    exact WP.mono (upd_ok A.P hH hF A.b A.h0 A.h2 A.h3 A.hdc A.hd₁ A.hd₃) fun t' ⟨b', g', _⟩ =>
      h.1.keep ⟨s, P, p, b'⟩ (g' .s6 (by decide)) (g' .s7 (by decide))
  refine two_seq (Ψ := LabF H) (lab3_taint (pins_of X (fun _ _ h => h.1) [])) (fun a t h => ?_) ?_
  · obtain ⟨⟨s, P, p, b⟩, _, h7⟩ := h
    refine wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_addi (imm := oDig) fun t₃ o₃ e₃ =>
      wp_nil ?_
    have k : Only [.a0, .a1, .a2] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    refine ⟨⟨s, P, p, b.only P.fits k⟩, ?_, ?_, ?_⟩
    · rw [o₃.get .a0, o₂.get .a0, e₁, b.s0, p.S]
    · rw [o₃.get .a1, e₂, o₁.get .s7, h7]
    · rw [e₃, o₂.get .s0, o₁.get .s0, b.s0, p.S]
  refine fin_ct (S := S) (vf := vO) cH hF fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  obtain ⟨⟨s₁, P₁, p₁, b₁⟩, x0, x1, x2⟩ := h₁
  obtain ⟨⟨s₂, P₂, p₂, b₂⟩, y0, y1, y2⟩ := h₂
  refine ⟨s₁, s₂, ⟨P₁.fits, b₁, by rw [x0, p₁.S], by rw [x2, p₁.S]⟩,
    ⟨P₂.fits, b₂, by rw [y0, p₂.S], by rw [y2, p₂.S]⟩, fun r hr => ?_,
    (b₁.agree (X.agree p₁)).1.trans (b₂.agree (X.agree p₂)).1.symm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [x0.trans y0.symm, x1.trans y1.symm, x2.trans y2.symm]

end

/-! ## MGF1, twice -/

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

/-! ## The function -/

/-- Two calls of `vg_rsa_public_precomputed_checked` from `AtCall`, for
entry states with the anchor's public data, agree on what the callee may
leak. -/
theorem call_ct {D : Nat} :
    RelCT isa (Two fun a t => ∃ s, PreO D s ∧ PubO a s ∧ ∃ EM, AtCall s EM t) Impl.RsaPkcs1Sig.RISCV64.pubCall
      fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, P₁, p₁, EM₁, c₁⟩, ⟨s₂, P₂, p₂, EM₂, c₂⟩⟩ => ⟨pdOk_of P₁ c₁,
    pdOk_of P₂ c₂, ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.sv.sp, c₂.sv.sp, fb, fb, p₁.sp, p₂.sp]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g0, c₂.g0, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g1, c₂.g1, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g2, c₂.g2, p₁.args 5 (by decide), p₂.args 5 (by decide)]
    · rw [c₁.g3, c₂.g3, p₁.args 6 (by decide), p₂.args 6 (by decide)]
    · rw [c₁.g4, c₂.g4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g5, c₂.g5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g6, c₂.g6, p₁.S, p₂.S]
    · rw [c₁.g7, c₂.g7, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [c₁.a0, c₂.a0, p₁.S, p₂.S]
  · rw [c₁.a1, c₂.a1, p₁.args 4 (by decide), p₂.args 4 (by decide)]
  · rw [c₁.g2, c₂.g2, c₁.g3, c₂.g3, words_entry c₁.mem P₁.kp ((P₁.sp).sub_left (sc_sub P₁)) P₁.wp,
      words_entry c₂.mem P₂.kp ((P₂.sp).sub_left (sc_sub P₂)) P₂.wp, p₁.w, p₂.w]
  · rw [c₁.g4, c₂.g4, c₁.g5, c₂.g5,
      bytes_entry c₁.mem P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega),
      bytes_entry c₂.mem P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega), p₁.e, p₂.e]

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) (fH : FitsF H)
  (fG : FitsF G) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs)

include cG fG hGh hGl hGv in
/-- `mgfXor`, with its lengths and offsets the anchor's. -/
theorem mgf_any (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfA S vO (PreO H.D) PubO (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXor G) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfA S vO (PreO H.D) PubO x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXor_ct (oaepOk H.D) hG cG fG x.2 hGh hGl hGv).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

/-- The checks passed, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 + (stackArg a 1).toNat ≤ (a.gpr .a3).toNat

theorem hk_of {D : Nat} {a s : State} (p : PubO a s) (h : HK D a) : 2 * D + 2 + mLen s ≤ kk s := by
  simp only [mLen, kk, p.args 1 (by decide), p.g .a3 (by decide)]; exact h

/-- `B` with the checks passed. -/
def Bk (D : Nat) (a t : State) : Prop := BO D a t ∧ HK D a

theorem bk_pins {D : Nat} {α : Type} {Φ : α → State → Prop} (A : α → State) (h : ∀ x t, Φ x t → BO D (A x) t) :
    Pins Φ [] := fun x t₁ t₂ h₁ h₂ =>
  ⟨((h x t₁ h₁).sp (oaepOk D)).trans ((h x t₂ h₂).sp (oaepOk D)).symm, fun _ h => nomatch h⟩

include cH fH cG fG hGh hGl hGv in
theorem encMain_ct : RelCT isa (Two fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Entered s t ∧ HK H.D a)
    (encMain H G) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨hE, _, _, _, _⟩ := offs
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  have X := oaepOk H.D
  -- `EM` before masking.
  refine two_seq (Ψ := fun a t => LabB H a t ∧ HK H.D a)
    (encEm_taint H fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => ?_)
    (fun a t ⟨s, P, p, E, hk⟩ => WP.mono (encEm_ok P rfl hD0 hD64 E (hk_of p hk)) fun t' ⟨b, g6, g7, _⟩ =>
      ⟨⟨⟨s, P, p, b⟩, by rw [g6, p.g _ (by decide)], by rw [g7, p.g _ (by decide)]⟩, hk⟩) ?_
  · have f₁ := E₁.base.agree (X.agree p₁)
    have f₂ := E₂.base.agree (X.agree p₂)
    refine ⟨f₁.1.trans f₂.1.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [E₁.t2, E₂.t2, p₁.args 0 (by decide), p₂.args 0 (by decide)]
    · rw [E₁.t3, E₂.t3, p₁.args 1 (by decide), p₂.args 1 (by decide)]
    · rw [E₁.t4, E₂.t4, p₁.args 2 (by decide), p₂.args 2 (by decide)]
    · exact f₁.2.1.trans f₂.2.1.symm
    · exact (f₁.2.2 _ (by decide)).trans (f₂.2.2 _ (by decide)).symm
  -- The label's hash, and `lHash`.
  refine two_seq (Ψ := Bk H.D) ((hashLabel_ct hH cH fH).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨⟨s, P, p, b⟩, h6, h7⟩, hk⟩ => WP.mono (hashLabel_ok P hH fH b
      (by rw [h6, p.g _ (by decide)]) (by rw [h7, p.g _ (by decide)])) fun t' ⟨b', _⟩ =>
      ⟨⟨s, P, p, b'⟩, hk⟩) ?_
  refine two_seq (Ψ := Bk H.D) (copyLh_taint H (pins_of X (fun _ _ h => h.1) [.s0]))
    (fun a t ⟨⟨s, P, p, b⟩, hk⟩ => WP.mono (copyLh_ok P hH rfl b) fun t' ⟨b', _⟩ => ⟨⟨s, P, p, b'⟩, hk⟩) ?_
  -- `DB` with MGF1 of the seed.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, (a.gpr .a3).toNat - H.D - 1)
  refine two_seq (Ψ := fun a t => (MgfA S vO (PreO H.D) PubO (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (bk_pins id fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, b⟩, hk⟩ => ?_) ?_
  · have k2 := P.k2
    have ek : (a.gpr .a3).toNat = (s.gpr .a3).toNat := by rw [p.g .a3 (by decide)]
    refine wp_addi (imm := oEm + 1) (h := by omega) fun t₁ o₁ e₁ => wp_li (imm := H.D) (by omega)
      fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₃ o₃ e₃ =>
      wp_subi (imm := H.D + 1) (h := by omega) fun t₄ o₄ e₄ => wp_nil ?_
    have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfA S vO (PreO H.D) PubO 1 H.D (1 + H.D) ((a.gpr .a3).toNat - H.D - 1) a t₄ ∧
      MFit 1 H.D (1 + H.D) ((a.gpr .a3).toNat - H.D - 1)) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.fits k₄, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inl (by omega), by omega⟩⟩, hk⟩
    · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, b.s0, p.S, hE]
    · rw [o₄.get .s7, o₃.get .s7, e₂]
    · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, b.s0, p.S, hE, Nat.zero_add]
    · rw [e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, b.s1, sub_k (by omega)]; congr 1; omega
  refine two_seq (Ψ := Bk H.D) ((mgf_any hG cG fG hGh hGl hGv q₁).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨⟨s, P, p, b, h6, h7, h8, h9⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXor_ok P.fits hG fG hGh hGl hGv hf b (by rw [h6, p.S]) h7 (by rw [h8, p.S]) h9)
      fun t' ⟨b', _⟩ => ⟨⟨s, P, p, b'⟩, hk⟩) ?_
  -- The seed with MGF1 of `maskedDB`.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, (a.gpr .a3).toNat - H.D - 1, 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfA S vO (PreO H.D) PubO (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (bk_pins id fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, b⟩, hk⟩ => ?_) ?_
  · have k2 := P.k2
    have ek : (a.gpr .a3).toNat = (s.gpr .a3).toNat := by rw [p.g .a3 (by decide)]
    refine wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₁ o₁ e₁ =>
      wp_subi (imm := H.D + 1) (h := by omega) fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1) (h := by omega)
      fun t₃ o₃ e₃ => wp_li (imm := H.D) (by omega) fun t₄ o₄ e₄ => wp_nil ?_
    have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfA S vO (PreO H.D) PubO (1 + H.D) ((a.gpr .a3).toNat - H.D - 1) 1 H.D a t₄ ∧
      MFit (1 + H.D) ((a.gpr .a3).toNat - H.D - 1) 1 H.D) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.fits k₄, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inr (by omega), by omega⟩⟩, hk⟩
    · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, b.s0, p.S, hE, Nat.zero_add]
    · rw [o₄.get .s7, o₃.get .s7, e₂, o₁.get .s1, b.s1, sub_k (by omega)]; congr 1; omega
    · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, b.s0, p.S, hE]
    · rw [e₄]
  refine two_seq (Ψ := Bk H.D) ((mgf_any hG cG fG hGh hGl hGv q₂).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨⟨s, P, p, b, h6, h7, h8, h9⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXor_ok P.fits hG fG hGh hGl hGv hf b (by rw [h6, p.S]) h7 (by rw [h8, p.S]) h9)
      fun t' ⟨b', _⟩ => ⟨⟨s, P, p, b'⟩, hk⟩) ?_
  -- The public-key operation.
  exact two_seq (pubArgs_taint (bk_pins id fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, b⟩, _⟩ =>
    WP.mono (pubArgs_ok P b rfl) fun t' h => ⟨s, P, p, _, h⟩) call_ct

theorem entered_only {s t t' : State} {rs : List Reg} {D : Nat} (P : PreO D s) (E : Entered s t)
    (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ fixed ++ ([.s6, .s7, .t2, .t3, .t4] : List Reg) := by decide) : Entered s t' := by
  have g : ∀ r ∈ [Reg.s6, .s7, .t2, .t3, .t4], t'.gpr r = t.gpr r := fun r hr =>
    o.gpr r fun h => hrs r h (List.mem_append_right _ hr)
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (List.mem_append_left _ h'), (g _ (by decide)).trans E.s6,
    (g _ (by decide)).trans E.s7, (g _ (by decide)).trans E.t2, (g _ (by decide)).trans E.t3,
    (g _ (by decide)).trans E.t4⟩

include cH fH cG fG hGh hGl hGv in
theorem checks_ct : RelCT isa (Two fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Entered s t) (checks H G)
    fun _ _ => True := by
  have hD64 := hH.hD64
  let K := fun (a : State) => (a.gpr .a3).toNat
  refine two_seq (Ψ := fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Entered s t ∧
      (t.gpr .a0 != 0) = decide (K a < 2 * H.D + 2))
    (chkK_taint H (bk_pins id fun _ _ ⟨s, P, p, E⟩ => ⟨s, P, p, E.base⟩)) (fun a t ⟨s, P, p, E⟩ => ?_) ?_
  · have k2 := P.k2
    have ka : (a.gpr .a3).toNat ≤ 1024 := by rw [← p.g .a3 (by decide)]; exact P.k2
    refine wp_li (imm := 2 * H.D + 2) (by omega) fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ =>
      wp_srl fun t₃ o₃ e₃ => wp_nil ?_
    have k₃ : Only [.a0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    refine ⟨s, P, p, entered_only P E k₃, ?_⟩
    rw [e₃, e₂, e₁, o₁.get .s1, E.base.s1, ← ofNat_toNat (s.gpr .a3), p.g .a3 (by decide)]
    exact ne_zero_ltBit (by omega) (by omega)
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, c₁⟩ ⟨_, _, _, _, c₂⟩ => by rw [eval_nonzero, eval_nonzero, c₁, c₂])
    (fail_taint (pins_of (oaepOk H.D) (fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P, p, E.base⟩) [.s1, .s2])) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Entered s t ∧ 2 * H.D + 2 ≤ K a ∧
      (t.gpr .a0 != 0) = decide (K a - (2 * H.D + 2) < (stackArg a 1).toNat))
    (chkMsg_taint H (bk_pins id fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P, p, E.base⟩))
    (fun a t ⟨⟨s, P, p, E, c⟩, hc⟩ => ?_) ?_
  · have k2 := P.k2
    have hk : 2 * H.D + 2 ≤ K a := by rw [eval_nonzero, c] at hc; simpa using hc
    have ek : K a = (s.gpr .a3).toNat := by simp only [K]; rw [p.g .a3 (by decide)]
    refine wp_li (imm := 2 * H.D + 2) (by omega) fun t₄ o₄ e₄ => wp_sub fun t₅ o₅ e₅ =>
      wp_sub fun t₆ o₆ e₆ => wp_srl fun t₇ o₇ e₇ => wp_srl fun t₈ o₈ e₈ => wp_or fun t₉ o₉ e₉ => wp_nil ?_
    have k₉ : Only [.a0, .a1] t t₉ := (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉))))).mono
    refine ⟨s, P, p, entered_only P E k₉, hk, ?_⟩
    rw [e₉, e₈, o₇.get .t3, o₆.get .t3, o₅.get .t3, o₄.get .t3, E.t3, o₈.get .a1, e₇, e₆,
      o₅.get .t3, o₄.get .t3, E.t3, e₅, o₄.get .s1, E.base.s1, e₄,
      ← ofNat_toNat (s.gpr .a3), ← ofNat_toNat (stackArg s 1), Offset.ofNat_sub_ofNat (by omega),
      p.args 1 (by decide), ← ek]
    exact msgBit (by omega) (stackArg a 1).isLt
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, _, c₁⟩ ⟨_, _, _, _, _, c₂⟩ => by
      rw [eval_nonzero, eval_nonzero, c₁, c₂])
    (fail_taint (pins_of (oaepOk H.D) (fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P, p, E.base⟩) [.s1, .s2])) ?_
  refine (encMain_ct hH cH hG cG fH fG hGh hGl hGv).mono (fun _ _ h => ?_) fun _ _ h => h
  obtain ⟨a, ⟨⟨s₁, P₁, p₁, E₁, hk, c₁⟩, h₁⟩, ⟨⟨s₂, P₂, p₂, E₂, -, -⟩, -⟩⟩ := h
  rw [eval_nonzero, c₁] at h₁
  have : ¬ (K a - (2 * H.D + 2) < (stackArg a 1).toNat) := by simpa using h₁
  have hK : HK H.D a := by simp only [HK, K] at *; omega
  exact ⟨a, ⟨s₁, P₁, p₁, E₁, hK⟩, ⟨s₂, P₂, p₂, E₂, hK⟩⟩

variable {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)

include cH fH cG fG hGh hGl hGv hHh hHl in
theorem code_ct : RelCT isa (Two fun a s => PreO H.D s ∧ PubO a s) (encrypt H G) fun _ _ => True := by
  refine two_alloc (R := fun _ _ => True) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Entered s t)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocd, h₁.2.sp,
      h₂.2.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by subst e; exact WP.mono (entry_ok P) fun t E => ⟨s, P, p, E⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Saves s t)
    (checks_ct hH cH hG cG fH fG hGh hGl hGv) fun a t ⟨s, P, p, E⟩ =>
      WP.mono (checks_done hH hG fH fG hHh hHl hGh hGl hGv P E) fun t' d => ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaOaep.RISCV64


namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem leak_eq {a b c d : List Byte} {w w' : List (BitVec 64)} (ha : a.length = c.length)
    (hb : b.length = d.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (c ++ d).map (·.toNat) ++ w'.map (·.toNat)) :
    b = d ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = c ++ d := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  exact ⟨(List.append_inj hi ha).2, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

theorem pubO_of {H G : Spec.Mgf1.Hash} {s₁ s₂ : State}
    (h : (Spec.RsaOaep.encryptPrecomputedContract H G abi stackBytes).pub s₁ s₂) : PubO s₁ s₂ := by
  sig_pub [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    stackArgs_seven, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6⟩ := h
  obtain ⟨he, hw⟩ := leak_eq (by simp [bytesAt_length, h3]) (by simp [bytesAt_length, h5]) hl
  refine ⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, he.symm, hw.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm]

theorem pubO_refl (s : State) : PubO s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) (fH : FitsF H)
  (fG : FitsF G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
include cH cG fH fG hHh hHl hGh hGl hGv

theorem code_constantTime :
    ConstantTime isa (Spec.RsaOaep.encryptPrecomputedContract Hs Gs abi stackBytes).pre
      (Spec.RsaOaep.encryptPrecomputedContract Hs Gs abi stackBytes).pub (encrypt H G) :=
  RelCT.constantTime ((code_ct hH cH hG cG fH fG hGh hGl hGv hHh hHl).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨hHl ▸ preO_of h₁, pubO_refl s₁⟩, hHl ▸ preO_of h₂, pubO_of hp⟩) fun _ _ h => h)

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` against its shared
contract, given a state meeting it. -/
theorem enc_verified (hsat : ∃ s, (Spec.RsaOaep.encryptPrecomputedContract Hs Gs abi stackBytes).pre s) :
    Verified RISCV64.target (encrypt H G) (Spec.RsaOaep.encryptPrecomputedContract Hs Gs abi stackBytes) :=
  ⟨code_correct hH hG fH fG hHh hHl hGh hGl hGv, code_constantTime hH cH hG cG fH fG hHh hHl hGh hGl hGv, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting encryption's contract for `H`: a 512-bit modulus, a
one-byte `e`, an empty label and message, `H`'s seed, a working space of
2080 words, 16 words of `pre` at `0x5000`, and the stack arguments at
`sp`. -/
def encSatState (H : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10001 then 0x41
    else bif Nat.beq a.toNat 0x10011 then 0x42 else bif Nat.beq a.toNat 0x1001A then 0x02
    else bif Nat.beq a.toNat 0x10020 then 0x20 else bif Nat.beq a.toNat 0x10021 then 0x08
    else bif Nat.beq a.toNat 0x10029 then 0x50 else bif Nat.beq a.toNat 0x10030 then 16 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, H.len⟩, ⟨0x5000, 128⟩, ⟨0x10000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

/-- The hash functions the label is hashed with. -/
def labelHashes : List Spec.Mgf1.Hash :=
  [Spec.Mgf1.sha1, Spec.Mgf1.sha224, Spec.Mgf1.sha256, Spec.Mgf1.sha384, Spec.Mgf1.sha512, Spec.Mgf1.sha512_224,
    Spec.Mgf1.sha512_256]

theorem enc_sat {H : Spec.Mgf1.Hash} (G : Spec.Mgf1.Hash) (hH : H ∈ labelHashes) :
    ∃ s, (Spec.RsaOaep.encryptPrecomputedContract H G abi stackBytes).pre s := by
  simp only [labelHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha512_256


/-! ## The hash functions -/

theorem ct_mono {pre pre' : State → Prop} {pub pub' : State → State → Prop} {c : Prog isa}
    (h : ConstantTime isa pre pub c) (hp : ∀ s, pre' s → pre s) (hq : ∀ s₁ s₂, pub' s₁ s₂ → pub s₁ s₂) :
    ConstantTime isa pre' pub' c :=
  fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ => h _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (hq _ _ hpub) e₁ e₂

theorem sha1CT : HashCT Sha1.ok where
  init := ct_mono Proof.Sha1.RISCV64.Stream.init_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  upd := ct_mono Proof.Sha1.RISCV64.Stream.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Sha1.RISCV64.Stream.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha256CT : HashCT Sha256Family.ok256 where
  init := ct_mono Proof.Sha256.RISCV64.Stream.init_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  upd := ct_mono Proof.Sha256.RISCV64.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Sha256.RISCV64.Stream.Finalize.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha224CT : HashCT Sha256Family.ok224 where
  init := ct_mono Proof.Sha256.RISCV64.Stream.init224_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  upd := ct_mono Proof.Sha256.RISCV64.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Sha256.RISCV64.Stream.Finalize.finalize224_verified.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha512FamilyCT (iv : Spec.Sha512.HashValue) {D : Nat} {initN finN : String} {finC : Prog isa}
    {HF : Spec.Hmac.HashFunction} {hB : HF.blockSize = 128} {hD : 0 < D ∧ D ≤ 64}
    {hinit : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith iv) (Proof.Sha512.initRISCV64 iv)}
    {hfin : Verified RISCV64.target finC (Proof.Sha512.finalizeDRISCV64 D)} {hfs : sdepth finC ≤ 208}
    {htake : ∀ x, HF.hash x = (Spec.Sha512.finalHash iv x).take D} :
    HashCT (Sha512Family.ok iv D initN finN finC HF hB hD hinit hfin hfs htake) where
  init := ct_mono hinit.2.1 (fun _ hs => hs) fun _ _ h => h
  upd := ct_mono Proof.Sha512.RISCV64.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono hfin.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha384CT : HashCT Sha384.ok := sha512FamilyCT _
theorem sha512CT : HashCT Sha512.ok := sha512FamilyCT _
theorem sha512_224CT : HashCT Sha512_224.ok := sha512FamilyCT _
theorem sha512_256CT : HashCT Sha512_256.ok := sha512FamilyCT _

/-- A hash function's streaming functions, with what the proofs need. -/
structure Link (H : Hash) where
  ok : HashOK H
  ct : HashCT ok
  fits : FitsF H
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  len : G.len = H.D
  mem : G ∈ labelHashes

theorem Link.valid {H : Hash} (l : Link H) : Proof.Mgf1.Valid l.G :=
  ⟨by rw [l.len]; exact l.ok.hD0, fun x => by rw [l.hash, l.ok.hashLen, l.len]⟩

def sha1L : Link Sha1.hash :=
  ⟨Sha1.ok, sha1CT, by decide, Spec.Mgf1.sha1, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha224L : Link Sha256Family.hash224 :=
  ⟨Sha256Family.ok224, sha224CT, by decide, Spec.Mgf1.sha224, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha256L : Link Sha256Family.hash256 :=
  ⟨Sha256Family.ok256, sha256CT, by decide, Spec.Mgf1.sha256, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha384L : Link Sha384.hash :=
  ⟨Sha384.ok, sha384CT, by decide, Spec.Mgf1.sha384, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha512L : Link Sha512.hash :=
  ⟨Sha512.ok, sha512CT, by decide, Spec.Mgf1.sha512, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha512_224L : Link Sha512_224.hash :=
  ⟨Sha512_224.ok, sha512_224CT, by decide, Spec.Mgf1.sha512_224, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha512_256L : Link Sha512_256.hash :=
  ⟨Sha512_256.ok, sha512_256CT, by decide, Spec.Mgf1.sha512_256, fun _ => rfl, rfl, by simp [labelHashes]⟩

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` for the linked hash
functions. -/
theorem link_verified {H G : Hash} (lh : Link H) (lg : Link G) :
    Verified RISCV64.target (Impl.RsaOaep.RISCV64.encrypt H G)
      (Spec.RsaOaep.encryptPrecomputedContract lh.G lg.G abi stackBytes) :=
  enc_verified lh.ok lh.ct lg.ok lg.ct lh.fits lg.fits lh.hash lh.len lg.hash lg.len lg.valid
    (enc_sat lg.G lh.mem)

end VG.Proof.RsaOaep.RISCV64
