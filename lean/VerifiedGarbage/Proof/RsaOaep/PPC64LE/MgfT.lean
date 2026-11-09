module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfStepsT
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Mgf
public import VerifiedGarbage.Proof.RsaOaep.Mask
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# RSAES-OAEP on PPC64LE: MGF1 with the hash function of a table

Untrusted: everything here is checked by Lean. `roundT_ok`: a round of
`mgfXorT` XORs the next block of the mask into `dst` (`MgfIT`, the invariant:
after `c` rounds, the first `min(c hLen, dstLen)` bytes of the mask are
XORed in); `mgfXorT_ok`: `dst ⊕= MGF1(src, dstLen)` in `EM`'s place (`mixV`).
As on AArch64 (`Proof/RsaOaep/AArch64/MgfT.lean`), with the hash function
`G` of the table that is our stack argument `j` (`TabS`): each call through
it (`tcallT_ok`) runs as `G`'s (`initT_ok`, `updT_ok`, `finT_ok`), the
addresses of the statics being those of the entry.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_mov wp_nil eval_nonzero)
open VG.Impl.RsaOaep.PPC64LE (Fns tcall tword)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

/-- After `c` rounds: `Base`, MGF1's registers, and the first
`min(c D, dstLen)` bytes of the mask `mk` XORed into `dst` in `EM`'s place,
whose view was `V`. -/
structure MgfIT (S : State → Addr) (vf : State → Reg → BitVec 64) (s : State) (V : Nat → Byte) (mk : List Byte) (src srcLen dst dstLen D c : Nat) (v : State) :
    Prop where
  base : Base S vf s v
  r24 : v.gpr .r24 = off (S s) src
  r25 : v.gpr .r25 = BitVec.ofNat 64 srcLen
  r26 : v.gpr .r26 = off (S s) dst
  r27 : v.gpr .r27 = BitVec.ofNat 64 dstLen
  r28 : v.gpr .r28 = BitVec.ofNat 64 c
  r29 : v.gpr .r29 = BitVec.ofNat 64 (c * D)
  em : ∀ o < oSt, view v.mem (S s) o = mixV V mk dst (min (c * D) dstLen) o
  sy : v.syms = s.syms

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s)
include P

/-! ## A call through the table -/

omit P in
theorem not_r12 {r : Reg} (hr : r ∈ preserved) : r ∉ [.r12] := fun h' => by
  rw [List.mem_singleton] at h'; subst h'; exact absurd hr (by decide)

section TCall
variable {G : Hash} {f : Fns} {j : Nat} {p : Addr} (T : TabS G f j S s p)
include T

omit P in
/-- The call of the table's function `k`, among `ts`, which reaches `n`, as
the call of `n` from the state the load of its address leaves. -/
theorem tcallT_ok {t : State} (h : Base S vf s t) (sy : t.syms = s.syms) {k : Nat} (hk : k < 3)
    {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hf : ts.find? (fun q => s.syms q.1 == s.syms n) = some (n, c))
    (hw : s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 = s.syms n) {Q : State → Prop}
    (kk : ∀ t', Only [.r12] t t' → t'.syms = t.syms → WP isa (.call n c) t' Q) : WP isa (tcall j k ts) t Q := by
  show WP isa (.seq (.block (tword .r12 j k ++ [])) (Code.icalls .bctrl ts)) t Q
  refine WP.seq (WP.of_syms (wp_tword T h (by omega) (by decide) fun t' o e => wp_nil fun sy' => ?_))
  refine WP.icalls_of_call (a := t'.gpr .r12) rfl ?_ (kk t' o sy')
  show ts.find? (fun q => t'.syms q.1 == t'.gpr .r12) = _
  rw [e, hw, sy', sy]; exact hf

/-- `init` through the table. -/
theorem initT_ok (hG : HashOK G) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    (h3 : t.gpr .r3 = off (S s) oSt) :
    WP isa (tcall j 0 f.init) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, G.S)] ∧ hG.SH.Repr t'.mem (off (S s) oSt) []) ∧ t'.syms = s.syms :=
  tcallT_ok T h sy (k := 0) (by decide) T.ok.i (by rw [Nat.mul_zero, BitVec.add_zero]; exact T.mem.1)
    fun t' o sy' => WP.mono_syms (init_ok P hG (h.only P o) (by rw [o.get .r3]; exact h3))
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_r12 hq)),
        (Same.of_mem o.mem _).trans sm, r⟩, sy''.trans (sy'.trans sy)⟩

/-- `update` through the table. -/
theorem updT_ok (hG : HashOK G) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms) {dat : Addr} {len : Nat}
    (h3 : t.gpr .r3 = off (S s) oSt) (h5 : t.gpr .r5 = dat) (h6 : (t.gpr .r6).toNat = len)
    (h7 : t.gpr .r7 = off (S s) oW) (hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr))
    (hd₁ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oSt, G.S⟩) (hd₂ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oW, G.W⟩)
    (hd₃ : (cR s).Disjoint ⟨dat, len⟩) :
    WP isa (tcall j 1 f.upd) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, G.S), (oW, G.W)] ∧
      ∀ m, hG.SH.Repr t.mem (off (S s) oSt) m → t.gpr .r4 = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off (S s) oSt) (m ++ Spec.Sha256.bytesAt t.mem dat len)) ∧ t'.syms = s.syms :=
  tcallT_ok T h sy (k := 1) (by decide) T.ok.u (by rw [Nat.mul_one]; exact T.mem.2.1)
    fun t' o sy' => WP.mono_syms (upd_ok P hG (h.only P o) (by rw [o.get .r3]; exact h3) (by rw [o.get .r5]; exact h5)
      (by rw [o.get .r6]; exact h6) (by rw [o.get .r7]; exact h7) (by rw [o.rd, o.wr]; exact hdc) hd₁ hd₂ hd₃)
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_r12 hq)),
        (Same.of_mem o.mem _).trans sm, fun m hm h4 => by
          have := r m (by rw [o.mem]; exact hm) (by rw [o.get .r4]; exact h4)
          rwa [o.mem] at this⟩, sy''.trans (sy'.trans sy)⟩

/-- `finalize` through the table. -/
theorem finT_ok (hG : HashOK G) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    (h3 : t.gpr .r3 = off (S s) oSt) (h5 : t.gpr .r5 = off (S s) oDig) (h6 : t.gpr .r6 = off (S s) oW) :
    WP isa (tcall j 2 f.fin) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, G.S), (oDig, G.FD), (oW, G.W)] ∧
      ∀ m, hG.SH.Repr t.mem (off (S s) oSt) m → m.length < 2 ^ 64 → t.gpr .r4 = BitVec.ofNat 64 m.length →
        Spec.Sha256.bytesAt t'.mem (off (S s) oDig) G.FD = hG.fh m) ∧ t'.syms = s.syms :=
  tcallT_ok T h sy (k := 2) (by decide) T.ok.f (by rw [show 8 * 2 = 16 from rfl]; exact T.mem.2.2)
    fun t' o sy' => WP.mono_syms (fin_ok P hG (h.only P o) (by rw [o.get .r3]; exact h3) (by rw [o.get .r5]; exact h5)
      (by rw [o.get .r6]; exact h6))
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_r12 hq)),
        (Same.of_mem o.mem _).trans sm, fun m hm hl h4 =>
          r m (by rw [o.mem]; exact hm) hl (by rw [o.get .r4]; exact h4)⟩, sy''.trans (sy'.trans sy)⟩

end TCall

theorem roundT_ok {G : Hash} (hG : HashOK G) {f : Fns} {j : Nat} {p : Addr} (T : TabS G f j S s p)
    {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
    (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {V : Nat → Byte} {src srcLen dst dstLen c : Nat}
    (hf : MFit src srcLen dst dstLen) {v : State}
    (I : MgfIT S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D c v)
    (hc : c * G.D < dstLen) :
    WP isa (roundT f j) v fun v' => (v'.gpr .r12 != 0) = decide ((c + 1) * G.D < dstLen) ∧
      MgfIT S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D (c + 1) v' := by
  have F := hfits hG
  obtain ⟨_, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hD0 := hG.hD0
  have hD64 := hG.hD64
  have hDF := hG.hDF
  have hfs := hf.fs
  have hfd := hf.fd
  have hsep := hf.sep
  have hcD : c ≤ c * G.D := Nat.le_mul_of_pos_right c hD0
  -- The registers MGF1 keeps.
  let mg : List Reg := [.r24, .r25, .r26, .r27, .r28, .r29]
  have pm : ∀ r ∈ mg, r ∈ preserved := by decide
  refine WP.of_syms ?_
  -- `init`.
  refine WP.seq (WP.of_syms (wp_addi fun t₁ o₁ e₁ => wp_nil fun sy₁ => ?_))
  have b₁ := I.base.only P o₁
  refine WP.seq (WP.mono (initT_ok P T hG b₁ (sy₁.trans I.sy) (by rw [e₁, I.base.r14]))
    fun t₂ ⟨⟨b₂, g₂, s₂, r₂⟩, sy₂⟩ => ?_)
  have m₂ : ∀ r ∈ mg, t₂.gpr r = v.gpr r := fun r hr => by
    rw [g₂ r (pm r hr), o₁.gpr r (by revert r; decide)]
  -- `update` with `src`.
  refine WP.seq (WP.of_syms (wp_addi fun t₃ o₃ e₃ => wp_li (by decide) fun t₄ o₄ e₄ => wp_mov fun t₅ o₅ e₅ =>
    wp_mov fun t₆ o₆ e₆ => wp_addi fun t₇ o₇ e₇ => wp_nil fun sy₇ => ?_))
  have k₇ : Only [.r3, .r4, .r5, .r6, .r7] t₂ t₇ := (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))).mono
  have b₇ := b₂.only P k₇
  refine WP.seq (WP.mono (updT_ok P T hG b₇ (sy₇.trans sy₂) (dat := off (S s) src) (len := srcLen)
    (by rw [o₇.get .r3, o₆.get .r3, o₅.get .r3, o₄.get .r3, e₃, b₂.r14])
    (by rw [o₇.get .r5, o₆.get .r5, e₅, o₄.get .r24, o₃.get .r24, m₂ _ (by decide), I.r24])
    (by rw [o₇.get .r6, e₆, o₅.get .r25, o₄.get .r25, o₃.get .r25, m₂ _ (by decide), I.r25, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith)])
    (by rw [e₇, o₆.get .r14, o₅.get .r14, o₄.get .r14, o₃.get .r14, b₂.r14])
    (Covers.right (by rw [b₇.wr]; exact sc_cov P (by omega_arith))) (sdis (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
    (sdis (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (cR_dis P (by omega_arith)))
    fun t₈ ⟨⟨b₈, g₈, s₈, r₈⟩, sy₈⟩ => ?_)
  have m₈ : ∀ r ∈ mg, t₈.gpr r = v.gpr r := fun r hr => by
    rw [g₈ r (pm r hr), k₇.gpr r (by revert r; decide), m₂ r hr]
  have hsrc : Spec.Rsa.bytesAt t₇.mem (off (S s) src) srcLen = srcB V src srcLen := by
    rw [bytesAt_view]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [k₇.mem, s₂ _ (by omega_arith) (by simp; omega_arith), o₁.mem, I.em _ (by omega_arith), mixV, ifn (by omega_arith)]
  have hR8 : hG.SH.Repr t₈.mem (off (S s) oSt) (srcB V src srcLen) := by
    have := r₈ [] (by rw [k₇.mem]; exact r₂) (by rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, e₄]; rfl)
    rw [List.nil_append] at this
    exact hsrc ▸ this
  -- The counter, and `update` with it.
  refine WP.seq (WP.mono_syms (ctr_ok P b₈ (c := c) (by rw [m₈ _ (by decide), I.r28]) (by omega_arith))
    fun t₉ ⟨b₉, g₉, v₉, x3, x4, x5, x6, x7⟩ sy₉ => ?_)
  have m₉ : ∀ r ∈ mg, t₉.gpr r = v.gpr r := fun r hr => by rw [g₉ r (pm r hr), m₈ r hr]
  have hR9 : hG.SH.Repr t₉.mem (off (S s) oSt) (srcB V src srcLen) :=
    hG.congr t₈.mem t₉.mem (off (S s) oSt) _ (fun i hi => by
      have e := v₉ (oSt + i) (by omega_arith)
      simp only [view, ctrV] at e
      rw [ifn (by omega_arith)] at e
      rw [off_add]; exact e) hR8
  refine WP.seq (WP.mono (updT_ok P T hG b₉ (sy₉.trans sy₈) (dat := off (S s) oCtr) (len := 4) x3 x5 (by rw [x6]; rfl) x7
    (Covers.right (by rw [b₉.wr]; exact sc_cov P (by omega_arith))) (sdis (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
    (sdis (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (cR_dis P (by omega_arith)))
    fun t₁₀ ⟨⟨b₁₀, g₁₀, s₁₀, r₁₀⟩, sy₁₀⟩ => ?_)
  have m₁₀ : ∀ r ∈ mg, t₁₀.gpr r = v.gpr r := fun r hr => by rw [g₁₀ r (pm r hr), m₉ r hr]
  have hctr : Spec.Rsa.bytesAt t₉.mem (off (S s) oCtr) 4 = Spec.Rsa.i2osp c 4 := by
    rw [bytesAt_view]
    refine (List.map_congr_left fun i hi => ?_).trans ((RsaOaep.range_map_getD (n := 4)
      (xs := Spec.Rsa.i2osp c 4) (by rw [Proof.Mgf1.i2osp_length])).trans
      (List.take_of_length_le (by rw [Proof.Mgf1.i2osp_length])))
    have := List.mem_range.mp hi
    rw [v₉ _ (by omega_arith), ctrV, ifp (by omega_arith), Nat.add_sub_cancel_left]
  have hml : (srcB V src srcLen).length = srcLen := by simp [srcB]
  have hR10 : hG.SH.Repr t₁₀.mem (off (S s) oSt) (srcB V src srcLen ++ Spec.Rsa.i2osp c 4) := by
    have := r₁₀ _ hR9 (by rw [x4, m₈ _ (by decide), I.r25, hml])
    exact hctr ▸ this
  -- `finalize`.
  refine WP.seq (WP.of_syms (wp_addi fun t₁₁ o₁₁ e₁₁ => wp_addi fun t₁₂ o₁₂ e₁₂ => wp_addi fun t₁₃ o₁₃ e₁₃ =>
    wp_addi fun t₁₄ o₁₄ e₁₄ => wp_nil fun sy₁₄ => ?_))
  have k₁₄ : Only [.r3, .r4, .r5, .r6] t₁₀ t₁₄ := (o₁₁.trans (o₁₂.trans (o₁₃.trans o₁₄))).mono
  have b₁₄ := b₁₀.only P k₁₄
  have hl4 : (srcB V src srcLen ++ Spec.Rsa.i2osp c 4).length = srcLen + 4 := by
    rw [List.length_append, hml, Proof.Mgf1.i2osp_length]
  refine WP.seq (WP.mono (finT_ok P T hG b₁₄ (sy₁₄.trans sy₁₀) (by rw [o₁₄.get .r3, o₁₃.get .r3, o₁₂.get .r3, e₁₁, b₁₀.r14])
    (by rw [o₁₄.get .r5, e₁₃, o₁₂.get .r14, o₁₁.get .r14, b₁₀.r14])
    (by rw [e₁₄, o₁₃.get .r14, o₁₂.get .r14, o₁₁.get .r14, b₁₀.r14])) fun t₁₅ ⟨⟨b₁₅, g₁₅, s₁₅, r₁₅⟩, _⟩ => ?_)
  have m₁₅ : ∀ r ∈ mg, t₁₅.gpr r = v.gpr r := fun r hr => by
    rw [g₁₅ r (pm r hr), k₁₄.gpr r (by revert r; decide), m₁₀ r hr]
  have hfh := r₁₅ _ (by rw [k₁₄.mem]; exact hR10) (by rw [hl4]; omega_arith)
    (by rw [o₁₄.get .r4, o₁₃.get .r4, e₁₂, o₁₁.get .r25, m₁₀ _ (by decide), I.r25, hl4, BitVec.ofNat_add])
  have hdig : ∀ j < G.D, view t₁₅.mem (S s) (oDig + j) =
      (Gs.hash (srcB V src srcLen ++ Spec.Rsa.i2osp c 4)).getD j 0 := fun j hj => by
    rw [hGh, hG.hashTake, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj, ← List.getD_eq_getElem?_getD,
      ← hfh, view, ← off_add]
    simp only [Spec.Sha256.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show j < G.FD by omega_arith)]
    rfl
  -- Into `dst`.
  have hdc := Nat.min_le_left G.D (dstLen - c * G.D)
  have hn0 : 0 < min G.D (dstLen - c * G.D) := by omega_arith
  refine WP.seq (WP.seq (WP.mono (xorHeadT_ok T b₁₅ (G := G) (S := S s) (dst := dst) (dstLen := dstLen) (done := c * G.D)
    (by omega_arith) b₁₅.r14 (by rw [m₁₅ _ (by decide), I.r26]) (by rw [m₁₅ _ (by decide), I.r27])
    (by rw [m₁₅ _ (by decide), I.r29]) hc (by omega_arith)) fun t₁₆ ⟨k₁₆, x11, x12, x9⟩ => ?_))
  have b₁₆ := b₁₅.only P k₁₆
  refine WP.mono (xorLoop_ok (p := off (S s) (dst + c * G.D)) (q := off (S s) oDig) hn0 (by omega_arith) x11 x12 x9
    (fun j hj => by
      rw [off_add, k₁₆.rd, k₁₆.wr, b₁₅.wr, b₁₅.rd]; exact sc_inR P (by omega_arith) _)
    (sc_w P (by rw [k₁₆.wr, b₁₅.wr]) (by omega_arith))
    (fun j hj i hi => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith))
    (fun i hi j hj hij => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)))
    fun t₁₇ ⟨k₁₇, x₁₇⟩ => ?_
  have b₁₇ : Base S vf s t₁₇ := b₁₆.wb P k₁₇ (by rw [xorAt_length]; omega_arith) x₁₇
  have m₁₇ : ∀ r ∈ mg, t₁₇.gpr r = v.gpr r := fun r hr => by
    rw [k₁₇.gpr r (by revert r; decide), k₁₆.gpr r (by revert r; decide), m₁₅ r hr]
  -- The next counter.
  refine WP.mono (nextCtrT_ok T b₁₇ (G := G) (c := c) (done := c * G.D) (dstLen := dstLen)
    (by rw [m₁₇ _ (by decide), I.r28])
    (by rw [m₁₇ _ (by decide), I.r29]) (by rw [m₁₇ _ (by decide), I.r27]) (by omega_arith) (by omega_arith))
    fun t₁₈ ⟨k₁₈, x28, x29, x12'⟩ hsy => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  refine ⟨by rw [x12', hs1], b₁₇.only P k₁₈, by rw [k₁₈.get .r24, m₁₇ _ (by decide), I.r24],
    by rw [k₁₈.get .r25, m₁₇ _ (by decide), I.r25], by rw [k₁₈.get .r26, m₁₇ _ (by decide), I.r26],
    by rw [k₁₈.get .r27, m₁₇ _ (by decide), I.r27], x28, by rw [x29, hs1], fun o ho => ?_, hsy.trans I.sy⟩
  -- `EM`'s place.
  have hold : view t₁₅.mem (S s) o = view v.mem (S s) o := by
    have e₁₅ := s₁₅ o (by omega_arith) (by simp; omega_arith)
    have e₁₀ := s₁₀ o (by omega_arith) (by simp; omega_arith)
    have e₉ := v₉ o (by omega_arith)
    have e₈ := s₈ o (by omega_arith) (by simp; omega_arith)
    have e₂ := s₂ o (by omega_arith) (by simp; omega_arith)
    simp only [ctrV] at e₉
    rw [ifn (by omega_arith)] at e₉
    simp only [view] at *
    rw [e₁₅, k₁₄.mem, e₁₀, e₉, e₈, k₇.mem, e₂, o₁.mem]
  have hv : view t₁₈.mem (S s) o = if dst + c * G.D ≤ o ∧ o < dst + c * G.D + min G.D (dstLen - c * G.D) then
      view v.mem (S s) o ^^^ (Gs.hash (srcB V src srcLen ++ Spec.Rsa.i2osp c 4)).getD (o - (dst + c * G.D)) 0
      else view v.mem (S s) o := by
    rw [k₁₈.mem, x₁₇, k₁₆.mem, view_wb _ _ (by rw [xorAt_length]; omega_arith) (by omega_arith), xorAt_length]
    split
    · rename_i hx
      rw [xorAt_getD _ _ _ (by omega_arith), off_add, off_add, show dst + c * G.D + (o - (dst + c * G.D)) = o by omega_arith,
        ← hold]
      simp only [view]
      rw [← hdig _ (by omega_arith)]
      simp only [view]
    · exact hold
  rw [hv]
  by_cases hx : dst + c * G.D ≤ o ∧ o < dst + c * G.D + min G.D (dstLen - c * G.D)
  · have hs2 : G.D * (c + 1) = c * G.D + G.D := by rw [Nat.mul_comm]; exact hs1
    have hs3 : G.D * c = c * G.D := Nat.mul_comm _ _
    have hq : (o - dst) / G.D = c := Nat.div_eq_of_lt_le (by omega_arith) (by omega_arith)
    have hr : (o - dst) % G.D = o - (dst + c * G.D) := by
      rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]; omega_arith
    rw [ifp hx, I.em o ho, mixV, mixV, ifn (by omega_arith), ifp (by rw [hs1]; omega_arith),
      Proof.Mgf1.mgf1_getD hGv _ (show o - dst < dstLen by omega_arith), hGl, hq, hr]
  · rw [ifn hx, I.em o ho, mixV, mixV]
    by_cases hy : dst ≤ o ∧ o < dst + min (c * G.D) dstLen
    · rw [ifp hy, ifp (by rw [hs1]; omega_arith)]
    · rw [ifn hy, ifn (by rw [hs1]; omega_arith)]

/-- `dst ⊕= MGF1(src, dstLen)` in `EM`'s place, from `src`, `srcLen`, `dst`
and `dstLen` in `r24`–`r27`. -/
theorem mgfXorT_ok {G : Hash} (hG : HashOK G) {f : Fns} {j : Nat} {p : Addr} (T : TabS G f j S s p)
    {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
    (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {src srcLen dst dstLen : Nat}
    (hf : MFit src srcLen dst dstLen) {t : State} (h : Base S vf s t) (hsy : t.syms = s.syms)
    (h24 : t.gpr .r24 = off (S s) src)
    (h25 : t.gpr .r25 = BitVec.ofNat 64 srcLen) (h26 : t.gpr .r26 = off (S s) dst)
    (h27 : t.gpr .r27 = BitVec.ofNat 64 dstLen) :
    WP isa (mgfXorT f j) t fun t' => (Base S vf s t' ∧ ∀ o < oSt, view t'.mem (S s) o =
      mixV (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) src srcLen) dstLen) dst dstLen o) ∧
      t'.syms = s.syms := by
  have hpos := hf.pos
  have hD : 0 < G.D := hG.hD0
  refine WP.seq (WP.of_syms (wp_li (by decide) fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_nil fun sy₂ => ?_))
  have k₂ : Only [.r28, .r29] t t₂ := (o₁.trans o₂).mono
  have I0 : MgfIT S vf s (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) src srcLen) dstLen) src srcLen
      dst dstLen G.D 0 t₂ :=
    ⟨h.only P k₂, by rw [k₂.get .r24, h24], by rw [k₂.get .r25, h25], by rw [k₂.get .r26, h26],
      by rw [k₂.get .r27, h27], by rw [o₂.get .r28, e₁], by rw [e₂, Nat.zero_mul],
      fun o _ => by rw [mixV, ifn (by omega_arith), k₂.mem], sy₂.trans hsy⟩
  refine WP.loop (M := isa) (fun n w => ∃ c, n = dstLen - c * G.D ∧ c * G.D < dstLen ∧
      MgfIT S vf s (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) src srcLen) dstLen) src srcLen dst
        dstLen G.D c w)
    ?_ (dstLen - 0 * G.D) t₂ ⟨0, rfl, by omega_arith, I0⟩
  rintro n w ⟨c, rfl, hc, I⟩
  refine WP.mono (roundT_ok P hG T hGh hGl hGv hf I hc) fun w' ⟨hcf, I'⟩ => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  by_cases h' : (c + 1) * G.D < dstLen
  · exact .inr ⟨by rw [eval_nonzero, hcf, decide_eq_true h'], _, by omega_arith, c + 1, rfl, h', I'⟩
  · exact .inl ⟨by rw [eval_nonzero, hcf, decide_eq_false h'], ⟨I'.base,
      fun o ho => by rw [I'.em o ho, Nat.min_eq_right (by omega_arith)]⟩, I'.sy⟩

end

end VG.Proof.RsaOaep.PPC64LE
