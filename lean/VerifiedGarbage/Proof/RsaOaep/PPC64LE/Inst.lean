module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTTab
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pre
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Callee
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Tables
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Verified
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.VerifiedP

/-! ### `RsaOaep.PPC64LE.Verified`, which only this module used -/

section

/-! ### `RsaOaep.PPC64LE.CTMain`, which only this module used -/

section

/-! ### `RsaOaep.PPC64LE.CTLabel`, which only this module used -/

section

/-!
# RSAES-OAEP encryption on PPC64LE: two runs, and the label's hash

Untrusted: everything here is checked by Lean. Two runs are compared through
an anchor `a`, a state with their public data (`PubO`): the pointers and
lengths, `e`'s bytes and the precomputed values; `BO D a t`: `t` has `Base`
from an entry state with `a`'s public data (`B`, `Proof/RsaOaep/PPC64LE/CTBase.lean`,
with `oaepOk`). The label's hash is through its table, in two runs
`hashLabelT_ct` (`CTMgfT.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo Two Pins two_post wp_li wp_addi wp_mov wp_nil)

/-- The public data of an entry state `s` is the anchor `a`'s. -/
structure PubO (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = a.gpr r
  args : ∀ i < 8, stackArg s i = stackArg a i
  e : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r7) (a.gpr .r8).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat

theorem PubO.S {a s : State} (p : PubO a s) : S s = stackArg a 4 := p.args 4 (by decide)

/-- `PubO` gives what the shared code needs. -/
theorem oaepOk (D : Nat) : Ok S vO (PreO D) PubO where
  fits P := P.fits
  agree {a s} p := ⟨p.sp, p.S, fun r hr => by
    simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vO]
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.args 6 (by decide)
    · exact p.args 7 (by decide)
    · exact p.args 5 (by decide)⟩

/-- `t` has `Base` from an entry state with `a`'s public data. -/
abbrev BO (D : Nat) : State → State → Prop := B S vO (PreO D) PubO

end VG.Proof.RsaOaep.PPC64LE

end

end

/-! ### `RsaOaep.PPC64LE.Correct`, which only this module used -/

section

/-! ### `RsaOaep.PPC64LE.Pub`, which only this module used -/

section

/-! ### `RsaOaep.PPC64LE.Main`, which only this module used -/

section

/-!
# RSAES-OAEP encryption on PPC64LE: `EM`

Untrusted: everything here is checked by Lean. `em_ok`: `EM` before masking
(`encEm`, the label's hash with the table that is our stack argument 8, and
`copyLh`, as `RsaOaep.EmAt`); `mask_ok`: `DB`
masked with MGF1 of the seed and the seed with MGF1 of `maskedDB`, which
leaves EME-OAEP's encoding at `S` (`RsaOaep.emOf`, by `RsaOaep.em_mask`),
MGF1's hash function being that of the table that is our stack argument `j`
(`TabS`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_mov wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaOaep (mixV srcB EmAt emOf)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.RsaOaep.PPC64LE (hashLabelT)

/-- The seed's and the message's bytes, the label's, and the message's length,
from the entry state. -/
abbrev seedB (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 2) D
abbrev msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
abbrev labB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat
abbrev kk (s : State) : Nat := (s.gpr .r6).toNat
abbrev mLen (s : State) : Nat := (stackArg s 1).toNat

theorem sub_k {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega_arith), Nat.mod_eq_of_lt (a := x.toNat - a) (by omega_arith)]; omega_arith

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- `EM` before masking: `encEm`, the label's hash and `copyLh`. -/
theorem em_ok {H : Hash} (hH : HashOK H) {f : Impl.RsaOaep.PPC64LE.Fns} (TL : TabS H f 8 S s (stackArg s 8))
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x)
    (hD : H.D = D) {t : State} (E : Entered s t) (hsy : t.syms = s.syms) (hk : 2 * D + 2 + mLen s ≤ kk s)
    {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base S vO s t' → t'.syms = t.syms →
      EmAt (view t'.mem (S s)) (kk s) D (seedB D s) (Hs.hash (labB s)) (msgB s) (mLen s) → WP isa rest t' Q) :
    WP isa (.seq (encEm H) (.seq (hashLabelT f 8 .r19 .r20) (.seq (copyLh H) rest))) t Q := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  have hDF := hH.hDF
  obtain F := hfits hH
  obtain ⟨_, hSt, hDg, hCt, hW, hRs⟩ := offs
  refine WP.seq (WP.mono_syms (encEm_ok P hD (by omega_arith) (by omega_arith) E hk) fun t₁ ⟨b₁, hp⟩ y₁ => ?_)
  refine WP.seq (WP.mono (hashLabelT_ok P hH TL b₁ (y₁.trans hsy)) fun t₂ ⟨⟨b₂, _, s₂, d₂⟩, y₂⟩ => ?_)
  refine WP.seq (WP.mono_syms (copyLh_ok P hH hD b₂) fun t₃ ⟨b₃, _, m₃⟩ y₃ =>
    k t₃ b₃ (y₃.trans (y₂.trans hsy.symm)) ?_)
  obtain hlh : Spec.Rsa.bytesAt t₂.mem (off (S s) oDig) D = Hs.hash (labB s) := by
    rw [hHh, hH.hashTake, ← d₂, ← hD]
    simp only [Spec.Rsa.bytesAt]
    rw [← List.map_take, List.take_range, Nat.min_eq_left hDF]
  refine emAt_of hp hk P.k2 fun o ho => ?_
  rw [m₃, view_wb _ _ (by rw [bytesAt_length]; omega_arith) (by omega_arith), bytesAt_length, hlh,
    s₂ o (by omega_arith) (by simp; omega_arith)]

omit P in
/-- The bytes at `S`, from the view. -/
theorem bytesAt_S (m : Mem) (S : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m (off S 0) n = (List.range n).map (view m S) := by
  rw [bytesAt_view]; simp only [srcB, Nat.zero_add]

/-- `DB` masked with MGF1 of the seed, then the seed with MGF1 of `maskedDB`:
EME-OAEP's encoding at `S`. -/
theorem mask_ok {H G : Hash} (hG : HashOK G) {f : Impl.RsaOaep.PPC64LE.Fns} {j : Nat}
    (T : TabS G f j S s (stackArg s j)) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
    (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    {sd lh m : List Byte} (hsd : sd.length = D) (hlh : lh.length = D) (hm : m.length = mLen s)
    (hk : 2 * D + 2 + mLen s ≤ kk s) {t : State} (h : Base S vO s t) (hsy : t.syms = s.syms)
    (he : EmAt (view t.mem (S s)) (kk s) D sd lh m (mLen s)) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base S vO s t' → Spec.Rsa.bytesAt t'.mem (off (S s) 0) (kk s) = emOf Gs D (kk s) (mLen s) sd lh m →
      WP isa rest t' Q) :
    WP isa (.seq (.block (dbArgs H)) (.seq (mgfXorT f j) (.seq (.block (seedArgs H)) (.seq (mgfXorT f j) rest)))) t Q := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r6).toNat := rfl
  subst hD
  -- `DB` with MGF1 of the seed.
  refine WP.seq (WP.of_syms (wp_addi (h := by omega_arith) fun t₁ o₁ e₁ => wp_li (by omega_arith) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega_arith) fun t₃ o₃ e₃ => wp_subi (h := by omega_arith) fun t₄ o₄ e₄ => wp_nil fun sy₄ => ?_))
  obtain k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  obtain b₄ := h.only P.fits k₄
  refine WP.seq (WP.mono (mgfXorT_ok P.fits hG T hGh hGl hGv (src := 1) (srcLen := H.D) (dst := 1 + H.D)
    (dstLen := kk s - H.D - 1) ⟨by omega_arith, by omega_arith, .inl (by omega_arith), by omega_arith⟩ b₄
    (sy₄.trans hsy)
    (by rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, h.r14, hE])
    (by rw [o₄.get .r25, o₃.get .r25, e₂])
    (by rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, h.r14, hE, Nat.zero_add])
    (by rw [e₄, o₃.get .r15, o₂.get .r15, o₁.get .r15, h.r15, sub_k (by omega_arith)]; congr 1))
    fun t₅ ⟨⟨b₅, v₅⟩, sy₅⟩ => ?_)
  -- The seed with MGF1 of `maskedDB`.
  refine WP.seq (WP.of_syms (wp_addi (h := by omega_arith) fun t₆ o₆ e₆ => wp_subi (h := by omega_arith) fun t₇ o₇ e₇ =>
    wp_addi (h := by omega_arith) fun t₈ o₈ e₈ => wp_li (by omega_arith) fun t₉ o₉ e₉ => wp_nil fun sy₉ => ?_))
  obtain k₉ : Only [.r24, .r25, .r26, .r27] t₅ t₉ := (o₆.trans (o₇.trans (o₈.trans o₉))).mono
  obtain b₉ := b₅.only P.fits k₉
  refine WP.seq (WP.mono (mgfXorT_ok P.fits hG T hGh hGl hGv (src := 1 + H.D) (srcLen := kk s - H.D - 1) (dst := 1)
    (dstLen := H.D) ⟨by omega_arith, by omega_arith, .inr (by omega_arith), by omega_arith⟩ b₉ (sy₉.trans sy₅)
    (by rw [o₉.get .r24, o₈.get .r24, o₇.get .r24, e₆, b₅.r14, hE, Nat.zero_add])
    (by rw [o₉.get .r25, o₈.get .r25, e₇, o₆.get .r15, b₅.r15, sub_k (by omega_arith)]; congr 1)
    (by rw [o₉.get .r26, e₈, o₇.get .r14, o₆.get .r14, b₅.r14, hE])
    (by rw [e₉]))
    fun t₁₀ ⟨⟨b₁₀, v₁₀⟩, _⟩ => k t₁₀ b₁₀ ?_)
  -- `EM`.
  obtain hdb := he.db hlh hm hk
  generalize hDB : lh ++ Spec.RsaOaep.zeros (kk s - mLen s - 2 * H.D - 2) ++ 0x01 :: m = db at hdb
  obtain hdbl : db.length = kk s - H.D - 1 := by
    rw [← hDB]; simp [Spec.RsaOaep.zeros, hlh, hm]; omega_arith
  obtain V4 : view t₄.mem (S s) = view t.mem (S s) := by rw [k₄.mem]
  obtain V9 : view t₉.mem (S s) = view t₅.mem (S s) := by rw [k₉.mem]
  rw [V4] at v₅
  rw [V9] at v₁₀
  obtain hsrc : srcB (view t₅.mem (S s)) (1 + H.D) (kk s - H.D - 1) =
      srcB (mixV (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) 1 H.D) (kk s - H.D - 1)) (1 + H.D)
        (kk s - H.D - 1)) (1 + H.D) (kk s - H.D - 1) :=
    List.map_congr_left fun i hi => v₅ _ (by have := List.mem_range.mp hi; omega_arith)
  rw [bytesAt_S]
  refine (List.map_congr_left fun i hi => ?_).trans ((em_mask hGv (by omega_arith) hsd hdbl he.z0 he.sd hdb).trans ?_)
  · have hi := List.mem_range.mp hi
    rw [v₁₀ i (by omega_arith), hsrc, mixV, mixV]
    split
    · rw [v₅ i (by omega_arith)]
    · rw [v₅ i (by omega_arith)]
  · rw [← hDB]; rfl

end

end VG.Proof.RsaOaep.PPC64LE

end

end


/-!
# RSAES-OAEP encryption on PPC64LE: the public-key operation, and failing

Untrusted: everything here is checked by Lean. `pubArgs_ok`: the arguments
of `vg_rsa_public_precomputed_checked` (`AtCall`): `out`, `pre`, `e`, `EM`
at `S` and the rest of the working space; `call_ok`: the call writes RSAEP
of `EM` to `out` if `pre` holds the modulus' values (`AfterCall`), by its
contract (`Proof/RsaPkcs1Sig/PPC64LE/Callee.lean`); `fail_ok`: `encFail`
writes zeros to `out` and returns 0.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_mov wp_std wp_addSp wp_nil PdOk
  PdLay pdRd pdWr pdCall)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- `pre` holds the values of the modulus. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat)

/-- The working space the public operation gets. -/
abbrev rsaR (s : State) : Region := ⟨off (S s) oRsa, ((stackArg s 5).toNat - 1024) * 8⟩

/-- At the call of `vg_rsa_public_precomputed_checked`, from the entry state
`s`, with `EM` the encoding at `S`. -/
structure AtCall (s : State) (EM : List Byte) (t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  mem : Frame [kR s, SC S s] s.mem t.mem
  em : Spec.Rsa.bytesAt t.mem (off (S s) 0) (kk s) = EM
  g3 : t.gpr .r3 = s.gpr .r3
  g4 : t.gpr .r4 = s.gpr .r6
  g5 : t.gpr .r5 = stackArg s 6
  g6 : t.gpr .r6 = stackArg s 7
  g7 : t.gpr .r7 = s.gpr .r7
  g8 : t.gpr .r8 = s.gpr .r8
  g9 : t.gpr .r9 = off (S s) 0
  g10 : t.gpr .r10 = s.gpr .r6
  a0 : stackArg t 0 = off (S s) oRsa
  a1 : stackArg t 1 = BitVec.ofNat 64 ((stackArg s 5).toNat - 1024)

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

theorem scl : 1024 ≤ (stackArg s 5).toNat := by
  have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; omega_arith

theorem rsa_sub : Region.Sub (rsaR s) (scR s) := by
  have := scl P
  exact Offset.sub_base _ (by unfold oRsa; omega_arith)

theorem pubArgs_ok {t : State} {EM : List Byte} (h : Base S vO s t) (he : Spec.Rsa.bytesAt t.mem (off (S s) 0) (kk s) = EM) :
    WP isa (.block pubArgs) t (AtCall s EM) := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  obtain hsc := scl P
  have hk2 : kk s ≤ 1024 := P.k2
  simp only [pubArgs]
  refine wp_addSp fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_add fun t₃ o₃ e₃ => ?_
  rw [h.sp, BitVec.add_zero] at e₁
  obtain g12₃ : t₃.gpr .r12 = fb s := by rw [o₃.get .r12, o₂.get .r12, e₁]
  refine wp_std (a := fb s + BitVec.ofNat 64 96) (by rw [g12₃])
    (by rw [o₃.wr, o₂.wr, o₁.wr, h.wr]; exact in_fr s _ (by decide) (by decide)) fun t₄ m₄ => ?_
  refine wp_subi (h := by decide) fun t₅ o₅ e₅ => ?_
  refine wp_std (a := fb s + BitVec.ofNat 64 104) (by rw [o₅.get .r12, m₄.gpr, g12₃])
    (by rw [o₅.wr, m₄.wr, o₃.wr, o₂.wr, o₁.wr, h.wr]; exact in_fr s _ (by decide) (by decide)) fun t₆ m₆ => ?_
  refine wp_mov fun t₇ o₇ e₇ => wp_mov fun t₈ o₈ e₈ => wp_mov fun t₉ o₉ e₉ => wp_mov fun t₁₀ o₁₀ e₁₀ =>
    wp_mov fun t₁₁ o₁₁ e₁₁ => wp_mov fun t₁₂ o₁₂ e₁₂ => wp_addi fun t₁₃ o₁₃ e₁₃ => wp_mov fun t₁₄ o₁₄ e₁₄ =>
    wp_nil ?_
  obtain k₃ : Only [.r12, .r4, .r4] t t₃ := o₁.trans (o₂.trans o₃)
  obtain k₁₄ : Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] t₆ t₁₄ :=
    (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans o₁₄))))))).mono
  -- The two stack arguments.
  obtain fr₆ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] t₃.mem t₆.mem := by
    rw [m₆.mem, o₅.mem, m₄.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 96) (e := 96) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains (fb s) (d := 104) (e := 96) (by decide) (by decide) (by decide))
  obtain hK : Keep [.r12, .r4, .r5, .r3, .r6, .r7, .r8, .r9, .r10] t t₁₄ :=
    (k₃.keep.trans (m₄.keep.trans (o₅.keep.trans (m₆.keep.trans k₁₄.keep)))).mono
  obtain hfr : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] t.mem t₁₄.mem := by
    rw [k₁₄.mem, ← k₃.mem] at *; exact fr₆
  obtain hds : (slR s).Disjoint ⟨fb s + BitVec.ofNat 64 96, 16⟩ :=
    Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  obtain sv : Saves s t₁₄ := h.sv.keep hK hfr (fun r hr => by rw [List.mem_singleton.mp hr]; exact hds)
  have hsp : t₁₄.sp = fb s := sv.sp
  refine ⟨sv, hK.rd.trans h.rd, h.mem.trans (hfr.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨kR s, by simp, frame_sub s (by decide)⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← he]
    exact bytes_entry (A := ⟨fb s + BitVec.ofNat 64 96, 16⟩) (B := ⟨fb s + BitVec.ofNat 64 96, 16⟩)
      (hfr.mono fun r hr => by simp at hr ⊢; exact hr)
      ((P.fits.ksc).sub_left (frame_sub s (by decide)) |>.sub_right (sc_in (by omega_arith)))
      ((P.fits.ksc).sub_left (frame_sub s (by decide)) |>.sub_right (sc_in (by omega_arith))) (by omega_arith)
  · rw [o₁₄.get .r3, o₁₃.get .r3, o₁₂.get .r3, o₁₁.get .r3, o₁₀.get .r3, o₉.get .r3, o₈.get .r3, e₇, m₆.gpr,
      o₅.get .r16, m₄.gpr, k₃.get .r16, h.r16]
  · rw [o₁₄.get .r4, o₁₃.get .r4, o₁₂.get .r4, o₁₁.get .r4, o₁₀.get .r4, o₉.get .r4, e₈, o₇.get .r15, m₆.gpr,
      o₅.get .r15, m₄.gpr, k₃.get .r15, h.r15]
  · rw [o₁₄.get .r5, o₁₃.get .r5, o₁₂.get .r5, o₁₁.get .r5, o₁₀.get .r5, e₉, o₈.get .r21, o₇.get .r21, m₆.gpr,
      o₅.get .r21, m₄.gpr, k₃.get .r21, h.r21]
  · rw [o₁₄.get .r6, o₁₃.get .r6, o₁₂.get .r6, o₁₁.get .r6, e₁₀, o₉.get .r22, o₈.get .r22, o₇.get .r22, m₆.gpr,
      o₅.get .r22, m₄.gpr, k₃.get .r22, h.r22]
  · rw [o₁₄.get .r7, o₁₃.get .r7, o₁₂.get .r7, e₁₁, o₁₀.get .r17, o₉.get .r17, o₈.get .r17, o₇.get .r17, m₆.gpr,
      o₅.get .r17, m₄.gpr, k₃.get .r17, h.r17]
  · rw [o₁₄.get .r8, o₁₃.get .r8, e₁₂, o₁₁.get .r18, o₁₀.get .r18, o₉.get .r18, o₈.get .r18, o₇.get .r18, m₆.gpr,
      o₅.get .r18, m₄.gpr, k₃.get .r18, h.r18]
  · rw [o₁₄.get .r9, e₁₃, o₁₂.get .r14, o₁₁.get .r14, o₁₀.get .r14, o₉.get .r14, o₈.get .r14, o₇.get .r14,
      m₆.gpr, o₅.get .r14, m₄.gpr, k₃.get .r14, h.r14, hE]
  · rw [e₁₄, o₁₃.get .r15, o₁₂.get .r15, o₁₁.get .r15, o₁₀.get .r15, o₉.get .r15, o₈.get .r15, o₇.get .r15,
      m₆.gpr, o₅.get .r15, m₄.gpr, k₃.get .r15, h.r15]
  · show t₁₄.mem.readW (stackArgAddr t₁₄ 0) 64 = _
    rw [stackArgAddr_in, hsp, k₁₄.mem, m₆.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide)
      (by decide)) (by decide), o₅.mem, m₄.mem, Mem.readW_writeW_self64, e₃, o₂.get .r14, o₁.get .r14, h.r14, e₂]
  · show t₁₄.mem.readW (stackArgAddr t₁₄ 1) 64 = _
    rw [stackArgAddr_in, hsp, k₁₄.mem, m₆.mem, Mem.readW_writeW_self64, e₅, m₄.gpr, k₃.get .r23, h.r23,
      sub_k (by omega_arith)]

theorem oR_eq : oR s = ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [oR, P.ok]

theorem pdOk_of {t : State} {EM : List Byte} (ha : AtCall s EM t) : PdOk t := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  obtain hk1 := P.k1; have hk2 := P.k2
  obtain hsc := scl P
  have hsp : t.sp = fb s := ha.sv.sp
  obtain hsa : stackArgAddr t 0 = fb s + BitVec.ofNat 64 96 := by rw [stackArgAddr_in, hsp]
  obtain hS := S_fits P.fits
  have hwsc := P.wsc
  have eS : (S s).toNat = (stackArg s 4).toNat := rfl
  obtain hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq P]; exact P.ko
  obtain hem : Region.Sub ⟨off (S s) 0, (s.gpr .r6).toNat⟩ (scR s) :=
    fun x hx => sc_sub P x (sc_in (by unfold oRsa; omega_arith) x hx)
  obtain hfa : Region.Sub ⟨fb s + BitVec.ofNat 64 96, 16⟩ (kR s) := frame_sub s (by decide)
  obtain h1 : (stackArg t 1).toNat = (stackArg s 5).toNat - 1024 := by
    rw [ha.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  refine ⟨?hl, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, ha.a0, h1, hsa]
    exact {
      on := by rw [← oR_eq P]; exact P.op
      oe := by rw [← oR_eq P]; exact P.oe
      oi := by rw [← oR_eq P]; exact P.osc.sub_right hem
      os := by rw [← oR_eq P]; exact P.osc.sub_right (rsa_sub P)
      oa := (hko.sub_left hfa).symm
      ns := P.sp.symm.sub_right (rsa_sub P)
      es := P.es.sub_right (rsa_sub P)
      is := Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      sa := ((P.ksc.sub_left hfa).sub_right (rsa_sub P)).symm
      wo := by have := P.wo; rw [P.ok] at this; exact this
      wn := P.wp
      we := P.we
      wi := by
        show (S s + BitVec.ofNat 64 0).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
        rw [BitVec.add_zero]; unfold oRsa at hS; omega_arith
      ws := by
        show (S s + BitVec.ofNat 64 oRsa).toNat + ((stackArg s 5).toNat - 1024) * 8 ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa at *; omega_arith }
  case sp =>
    rw [hsp]; have := P.sp1
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes]; omega_arith
  case hrd =>
    simp only [pdRd]
    rw [ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, hsa, ha.rd, ha.sv.wr]
    obtain hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (fr s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    refine Covers.cons (hm _ (by rw [P.hrd]; simp)) (Covers.cons (hm _ (by rw [P.hrd]; simp))
      (Covers.cons (Covers.right (sc_cov P.fits (by unfold oRsa; omega_arith)))
        (Covers.one (in_fr' s _ _ (by decide) (by decide)) |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g3, ha.g4, ha.a0, h1, ha.sv.wr]
    refine Covers.cons (Covers.of_mem fun x hx => by
      rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ (by rw [P.hwr, oR_eq P]; simp))
      (Covers.cons ?_ Covers.nil)
    exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨scR s, by rw [P.hwr]; simp, oRsa, rfl, by simp only; unfold oRsa; omega_arith⟩
  case hk => rw [ha.g4]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g6, ha.g4]; exact P.hp
  case h10 => rw [ha.g10, ha.g4]
  case he1 => rw [ha.g8]; exact P.e1
  case he2 => rw [ha.g8, ha.g4]; exact P.e2
  case hs =>
    rw [ha.g4, h1]; have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; omega_arith

/-- After the call: what the restores need, and `out` written with RSAEP of
`EM` if `pre` holds the modulus' values. -/
structure AfterCall (s : State) (EM : List Byte) (t : State) : Prop where
  sv : Saves s t
  res : PreOk s → Spec.Rsa.written t.mem (s.gpr .r3) (kk s) ((t.gpr .r3).setWidth 32)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (kk s))
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) EM)

theorem call_ok {t : State} {EM : List Byte} (ha : AtCall s EM t) :
    WP isa Impl.RsaPkcs1Sig.PPC64LE.pubCall t (AfterCall s EM) := by
  have hk2 := P.k2
  refine pdCall (pdOk_of P ha) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g3, ha.g4, ha.a0, ha.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 5).isLt; omega_arith)] at hf
  obtain hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq P]; exact P.ko
  obtain hd : ∀ r ∈ [(⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region), rsaR s], (slR s).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hko.sub_left (slR_sub s)
    · exact (P.ksc.sub_left (slR_sub s)).sub_right (rsa_sub P)
  refine ⟨⟨hsp'.trans ha.sv.sp, hwr'.trans ha.sv.wr, fun r hr => (hpres r (by revert r; decide)).trans (ha.sv.hi r hr),
    ha.sv.sv.frame hf fun p hp' r hr => (hd r hr).sub_left (by
      have := saved_offs p hp'
      exact Offset.sub _ (n := 8) (by omega_arith) (by unfold oLr at *; omega_arith)),
    by
      rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left
        (Offset.sub _ (n := 8) (by decide) (by decide))) (by decide)]
      exact ha.sv.ls⟩, fun hc => ?_⟩
  obtain hw : Spec.Rsa.wordsAt t.mem (t.gpr .r5) (t.gpr .r6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat := by
    rw [ha.g5, ha.g6]; exact words_entry ha.mem P.kp ((P.sp).sub_left (sc_sub P)) P.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (by rw [ha.g4, bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g3, ha.g4, ha.g7, ha.g8, ha.g9, ha.em,
    bytes_entry ha.mem P.ke ((P.es.symm).sub_left (sc_sub P)) (by have := P.we; omega_arith)] at this
  exact this

/-- `encFail`: zeros to `out`, and 0. -/
theorem fail_ok {t : State} (h : Base S vO s t) :
    WP isa encFail t fun t' => Saves s t' ∧ t'.gpr .r3 = 0 ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .r3) (kk s) = List.replicate (kk s) 0 := by
  obtain hk1 := P.k1; have hk2 := P.k2
  have ek : kk s = (s.gpr .r6).toNat := rfl
  refine WP.seq (WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_nil ?_))
  obtain k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  obtain hout : ∀ i < kk s, InRegions t₃.wr (s.gpr .r3 + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [k₃.wr, h.wr]
    exact ⟨oR s, List.mem_cons_of_mem _ (by rw [P.hwr]; simp),
      Offset.contains_base _ (by rw [P.ok]; omega_arith) (by have := P.wo; omega_arith)⟩
  refine WP.mono (zero_ok (p := s.gpr .r3) (n := kk s) (b := 0) (by omega_arith) (by omega_arith)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r16]) (by rw [e₃ |> fun _ => o₃.get .r5, e₂, o₁.get .r15, h.r15]; simp)
    (by rw [e₃]; rfl) hout) fun t₄ ⟨k₄, m₄⟩ => wp_li (by decide) fun t₅ o₅ e₅ => wp_nil ?_
  obtain hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq P]; exact P.ko
  obtain hf : Frame [⟨s.gpr .r3, kk s⟩] t.mem t₅.mem := by
    have := Proof.RsaPkcs1Sig.frame_writeBytes t₃.mem (s.gpr .r3) (List.replicate (kk s) (0 : Byte))
    rw [List.length_replicate] at this
    rw [o₅.mem, m₄, ← k₃.mem] at *; exact this
  refine ⟨h.sv.keep ((k₃.keep.trans (k₄.trans o₅.keep)).mono (rs' := [.r3, .r4, .r5, .r6])) hf
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hko.sub_left (slR_sub s)), by rw [e₅]; rfl, ?_⟩
  have := Proof.RsaPkcs1Sig.bytesAt_writeBytes t₃.mem (s.gpr .r3) (List.replicate (kk s) (0 : Byte))
    (by simp; omega_arith)
  rw [List.length_replicate] at this
  rw [o₅.mem, m₄, this]

end

end VG.Proof.RsaOaep.PPC64LE

end

end


/-!
# RSAES-OAEP encryption on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The checks of the lengths
(`chkK`, `chkMsg`: `k < 2 hLen + 2` and `msg_len > k - 2 hLen - 2`, from the
top bits of differences), then either zeros and 0 (`fail_ok`) or `EM`
(`em_ok`, `mask_ok`, with the hash functions the tables') and RSAEP of it
(`call_ok`): if `pre` holds the modulus' values, RSAES-OAEP-ENCRYPT (RFC 8017
§7.1.1), all for the digest length of the label's table (`byLen_ok`,
`checks_D`). `code_correct`: the function against its contract, for tables
of `vs` (`tab_of`: each table is one of them, whose hash function it
names).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_sub wp_lsr wp_or wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.MdHashTable.PPC64LE (MVar tables fns3 Coh)
open VG.Impl.RsaOaep.PPC64LE (tword)

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem entered_only {s t t' : State} {rs : List Reg} {D : Nat} (P : PreO D s) (E : Entered s t)
    (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs ++ ([.r9, .r10, .r11] : List Reg) := by decide) : Entered s t' := by
  obtain g : ∀ r ∈ [Reg.r9, .r10, .r11], t'.gpr r = t.gpr r := fun r hr =>
    o.gpr r fun h => hrs r h (List.mem_append_right _ hr)
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (List.mem_append_left _ h'), (g _ (by decide)).trans E.r9,
    (g _ (by decide)).trans E.r10, (g _ (by decide)).trans E.r11⟩

/-- The code for a digest length, which is all it uses of the hash
function's shape. -/
theorem checks_D {G G' : Hash} (hD : G.D = G'.D) (f : Fns) : checks G f = checks G' f := by
  simp only [checks, encMain, encEm, copySeed, chkK, chkMsg, copyLh, dbArgs, seedArgs, hD]

/-- The result and `out`, from the entry state `s`: the octets `encrypt`
returns, or zeros. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s →
    Spec.Rsa.written s'.mem (s.gpr .r3) (kk s) ((s'.gpr .r3).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (kk s))
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (labB s) (msgB s) (seedB Hs.len s)))

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (PreOk s →
    Spec.Rsa.written t.mem (s.gpr .r3) (kk s) ((t.gpr .r3).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (kk s))
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (labB s) (msgB s) (seedB Hs.len s)))

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
  {f : Fns} {s : State} (P : PreO H.D s) (T : TabS G f 9 S s (stackArg s 9)) (TL : TabS H f 8 S s (stackArg s 8))
include hH hG hHh hHl hGh hGl hGv P T TL

omit hH hG hHh hGh hGl hGv T TL in
theorem fail_done {t : State} (h : Base S vO s t) (hl : kk s < 2 * H.D + 2 + mLen s) :
    WP isa encFail t (Done Hs Gs s) :=
  WP.mono (fail_ok P h) fun t' ⟨sv, h3, hb⟩ => ⟨sv, fun _ => by
    rw [Proof.RsaOaep.encrypt_none (by rw [bytesAt_length, bytesAt_length, hHl]; exact hl), h3]
    exact ⟨rfl, hb⟩⟩

theorem main_done {t : State} (E : Entered s t) (hsy : t.syms = s.syms) (hk : 2 * H.D + 2 + mLen s ≤ kk s) :
    WP isa (encMain H f) t (Done Hs Gs s) := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  refine em_ok P hH TL hHh rfl E hsy hk fun t₁ b₁ y₁ he => ?_
  refine mask_ok P hG T hGh hGl hGv rfl hD0 hD64 (bytesAt_length _ _ _)
    (by rw [hHh, hH.hashLen]) (bytesAt_length _ _ _) hk b₁ (y₁.trans hsy) he fun t₂ b₂ hem => ?_
  refine WP.seq (WP.mono (pubArgs_ok P b₂ hem) fun t₃ a₃ => WP.mono (call_ok P a₃) fun t₄ ⟨sv, res⟩ =>
    ⟨sv, fun hc => ?_⟩)
  obtain hs : (seedB Hs.len s).length = Hs.len := bytesAt_length _ _ _
  rw [Proof.RsaOaep.encrypt_some hs (by rw [bytesAt_length, bytesAt_length, hHl]; exact hk), bytesAt_length,
    bytesAt_length, hHl]
  exact res hc

theorem checks_done {t : State} (E : Entered s t) (hsy : t.syms = s.syms) : WP isa (checks H f) t (Done Hs Gs s) := by
  have hD64 := hH.hD64
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r6).toNat := rfl
  have b := E.base
  refine WP.seq (WP.of_syms (wp_li (by omega_arith) fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ =>
    wp_nil fun y₃ => ?_))
  obtain k₃ : Only [.r3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  obtain b₃ := b.only P.fits k₃
  obtain r3 : (t₃.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2) := by
    rw [e₃, e₂, e₁, o₁.get .r15, b.r15, ← ofNat_toNat (s.gpr .r6)]
    exact ne_zero_ltBit (by omega_arith) (by omega_arith)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P b₃
    (by rw [r3] at hc; simp at hc; omega_arith)) (fun hc => ?_)
  obtain hk : 2 * H.D + 2 ≤ kk s := by rw [r3] at hc; simp at hc; omega_arith
  refine WP.seq (WP.of_syms (wp_li (by omega_arith) fun t₄ o₄ e₄ => wp_sub fun t₅ o₅ e₅ => wp_sub fun t₆ o₆ e₆ =>
    wp_lsr fun t₇ o₇ e₇ => wp_lsr fun t₈ o₈ e₈ => wp_or fun t₉ o₉ e₉ => wp_nil fun y₉ => ?_))
  obtain k₉ : Only [.r3, .r4] t₃ t₉ := (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉))))).mono
  obtain b₉ := b₃.only P.fits k₉
  obtain r3' : (t₉.gpr .r3 != 0) = decide (kk s - (2 * H.D + 2) < mLen s) := by
    rw [e₉, e₈, o₇.get .r10, o₆.get .r10, o₅.get .r10, o₄.get .r10, k₃.get .r10, E.r10, o₈.get .r4, e₇, e₆,
      o₅.get .r10, o₄.get .r10, k₃.get .r10, E.r10, e₅, o₄.get .r15, k₃.get .r15, b.r15, e₄,
      ← ofNat_toNat (s.gpr .r6), ← ofNat_toNat (stackArg s 1), Offset.ofNat_sub_ofNat hk]
    exact msgBit (by omega_arith) (stackArg s 1).isLt
  obtain E₉ : Entered s t₉ := ⟨b₉, by rw [k₉.get .r9, k₃.get .r9]; exact E.r9,
    by rw [k₉.get .r10, k₃.get .r10]; exact E.r10, by rw [k₉.get .r11, k₃.get .r11]; exact E.r11⟩
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P b₉
    (by rw [r3'] at hc; simp at hc; omega_arith)) (fun hc => main_done hH hG hHh hHl hGh hGl hGv P T TL E₉
    (y₉.trans (y₃.trans hsy)) (by rw [r3'] at hc; simp at hc; omega_arith))

theorem code_ok (hl : H.D ∈ lens) : WP isa (encrypt f) s (Post Hs Gs s) := by
  have hD64 := hH.hD64
  refine WP.alloc (by decide) (by have := P.sp1; unfold frameBytes; omega_arith) ?_
  refine WP.seq (WP.mono_syms (entry_ok P) fun t E sy => ?_)
  -- The label's hash function's digest length to `r3`.
  refine WP.seq (WP.of_syms ?_)
  show WP isa (.block (tword .r3 8 6 ++ [])) t _
  refine wp_tword TL E.base (k := 6) (by decide) (d := .r3) (by decide) fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_
  obtain e3 : t₁.gpr .r3 = BitVec.ofNat 64 H.D := e₁.trans TL.d
  -- The code for that length.
  refine WP.seq (byLen_ok (D := H.D) (by omega_using [hD64])
    (F := fun u => Entered s u ∧ u.syms = s.syms ∧ u.gpr .r3 = BitVec.ofNat 64 H.D)
    (fun _ h => h.2.2) (fun u u' ⟨E', y', r3'⟩ o y => ⟨entered_only P E' o, y.trans y',
      by rw [o.get .r3]; exact r3'⟩) ?_ hl (fun x hx => (lens_certs x hx).1) t₁
    ⟨entered_only P E o₁, y₁.trans sy, e3⟩)
  intro u ⟨E', y', _⟩
  rw [checks_D (G := ofLen H.D) (G' := H) rfl]
  exact WP.mono (checks_done hH hG hHh hHl hGh hGl hGv P T TL E' y') fun t' ⟨sv, res⟩ =>
    WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hc => by rw [freed_mem, freed_gpr, hm, h3]; exact res hc⟩

end

/-- The label's hash function's table, on entry, if it is `w`'s: what its
calls need of it. -/
theorem tabS_entryL {D : Nat} {vs : List MVar} (hc : Coh vs) {s : State} (P : PreO D s)
    (hpw : (Proof.MdHashTable.PPC64LE.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : MVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 8) (FnTable.words isa s (Proof.MdHashTable.PPC64LE.tableOf w))) :
    TabS w.H (fns3 vs) 8 S s (stackArg s 8) := by
  refine Proof.MdHashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
    (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P)) (by
      rw [P.hrd]; iterate 6 apply List.mem_cons_of_mem
      exact List.mem_cons_self ..) P.ktl
    (P.stl.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega_using [])

/-- MGF1's table, on entry, if it is `w`'s: what MGF1 needs of it. -/
theorem tabS_entry {D : Nat} {vs : List MVar} (hc : Coh vs) {s : State} (P : PreO D s)
    (hpw : (Proof.MdHashTable.PPC64LE.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : MVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s (Proof.MdHashTable.PPC64LE.tableOf w))) :
    TabS w.H (fns3 vs) 9 S s (stackArg s 9) := by
  refine Proof.MdHashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
    (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P)) (by
      rw [P.hrd]; iterate 7 apply List.mem_cons_of_mem
      exact List.mem_cons_self ..) P.kt
    (P.st.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega_using [])

/-- The tables, on entry: each one of the tables of `vs`, which names its
hash function, and holds what the calls through it need. -/
theorem tab_of {vs : List MVar} (hc : Coh vs) {s : State} (h : (encSpec (tables vs)).pre s) :
    ∃ w₁ ∈ vs, ∃ w ∈ vs, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 8) = some w₁.l.G ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 9) = some w.l.G ∧
      ∀ {D : Nat}, PreO D s → TabS w₁.H (fns3 vs) 8 S s (stackArg s 8) ∧ TabS w.H (fns3 vs) 9 S s (stackArg s 9) := by
  obtain ⟨⟨T₁, hT₁, hh₁⟩, ⟨T, hT, hh⟩, hpw⟩ := spec_tab h
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain hpw' := hpw.sublist (List.sublist_append_left _ _)
  exact ⟨w₁, hw₁, w, hw, Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh₁).2.2.2,
    Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh).2.2.2,
    fun P => ⟨tabS_entryL hc P hpw' hw₁ hh₁, tabS_entry hc P hpw' hw hh⟩⟩

/-- The correctness of `vg_rsa_oaep_encrypt_precomputed`, against its
contract, for the tables of `vs`. -/
theorem code_correct {vs : List MVar} (hc : Coh vs) (s : State) (h : (encSpec (tables vs)).pre s) :
    ∃ t s', Exec isa (encrypt (fns3 vs)) s t s' ∧ abiPreserved s s' ∧ (encSpec (tables vs)).post s s' := by
  obtain ⟨w₁, -, w, -, hH, hG, hT⟩ := tab_of hc h
  obtain P : PreO w₁.H.D s := w₁.l.len ▸ preO_of h hH
  obtain ⟨TL, T⟩ := hT P
  obtain ⟨t, s', he, habi, hr⟩ := code_ok w₁.l.ok w.l.ok w₁.l.hash w₁.l.len w.l.hash w.l.len w.l.valid P T TL
    w₁.l.lens_mem
  refine ⟨t, s', he, habi, ?_⟩
  unfold encSpec
  sig_post [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig,
    Spec.MdHashTable.param, Abi.withTables, abi, argRegs, stackArgs_ten, List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  exact hr

end VG.Proof.RsaOaep.PPC64LE

end

end


/-!
# RSAES-OAEP encryption on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data leak alike: the code between the calls by the
taint analysis (`CTBlocks`), the hash functions' calls by their contracts
(`CTCalls`) through the tables, at the same addresses in both runs with
their functions at the same addresses (`hashLabelT_ct`), MGF1's loops on
counters both runs agree on (`mgfXorT_ct`), the digest length of the label's
table and the code for it (`tword_two`, `byLen_ct`), the
call of `vg_rsa_public_precomputed_checked` by its contract (`pdCallCT`),
and the branches on the public lengths (`two_ite`); what each run satisfies
between them follows from correctness.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi wp_mov
  wp_nil eval_nonzero pdCallCT)

/-- Two calls of `vg_rsa_public_precomputed_checked` from `AtCall`, for
entry states with the anchor's public data, agree on what the callee may
leak. -/
theorem call_ct {D : Nat} :
    RelCT isa (Two fun a t => ∃ s, PreO D s ∧ PubO a s ∧ ∃ EM, AtCall s EM t) Impl.RsaPkcs1Sig.PPC64LE.pubCall
      fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, P₁, p₁, EM₁, c₁⟩, ⟨s₂, P₂, p₂, EM₂, c₂⟩⟩ => ⟨pdOk_of P₁ c₁,
    pdOk_of P₂ c₂, ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.sv.sp, c₂.sv.sp, fb, fb, p₁.sp, p₂.sp]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g3, c₂.g3, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g4, c₂.g4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g5, c₂.g5, p₁.args 6 (by decide), p₂.args 6 (by decide)]
    · rw [c₁.g6, c₂.g6, p₁.args 7 (by decide), p₂.args 7 (by decide)]
    · rw [c₁.g7, c₂.g7, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g8, c₂.g8, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g9, c₂.g9, p₁.S, p₂.S]
    · rw [c₁.g10, c₂.g10, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [c₁.a0, c₂.a0, p₁.S, p₂.S]
  · rw [c₁.a1, c₂.a1, p₁.args 5 (by decide), p₂.args 5 (by decide)]
  · rw [c₁.g5, c₂.g5, c₁.g6, c₂.g6, words_entry c₁.mem P₁.kp ((P₁.sp).sub_left (sc_sub P₁)) P₁.wp,
      words_entry c₂.mem P₂.kp ((P₂.sp).sub_left (sc_sub P₂)) P₂.wp, p₁.w, p₂.w]
  · rw [c₁.g7, c₂.g7, c₁.g8, c₂.g8,
      bytes_entry c₁.mem P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega_arith),
      bytes_entry c₂.mem P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega_arith), p₁.e, p₂.e]

/-- The precondition, with MGF1's table, `G`'s, and the label's hash
function's, `H`'s, on entry. -/
def PreT (D : Nat) (G H : Hash) (f : Fns) (s : State) : Prop :=
  PreO D s ∧ TabS G f 9 S s (stackArg s 9) ∧ TabS H f 8 S s (stackArg s 8)

/-- The public data, with both tables at the anchor's addresses and their
hash functions' functions at the anchor's addresses. -/
def PubT (G H : Hash) (a s : State) : Prop :=
  PubO a s ∧ stackArg s 9 = stackArg a 9 ∧ s.syms G.initN = a.syms G.initN ∧ s.syms G.updN = a.syms G.updN ∧
    s.syms G.finN = a.syms G.finN ∧ stackArg s 8 = stackArg a 8 ∧ s.syms H.initN = a.syms H.initN ∧
    s.syms H.updN = a.syms H.updN ∧ s.syms H.finN = a.syms H.finN

theorem okT (D : Nat) (G H : Hash) (f : Fns) : Ok S vO (PreT D G H f) (PubT G H) :=
  ⟨fun P => P.1.fits, fun p => (oaepOk D).agree p.1⟩

theorem tabT (D : Nat) (G H : Hash) (f : Fns) : TabA G f 9 S (PreT D G H f) (PubT G H) :=
  ⟨fun P => P.2.1, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2.1⟩

theorem tabL (D : Nat) (G H : Hash) (f : Fns) : TabA H f 8 S (PreT D G H f) (PubT G H) :=
  ⟨fun P => P.2.2, fun p => p.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.1,
    fun p => p.2.2.2.2.2.2.2.2⟩

/-- `t` has `Base` from an entry state with `G`'s table and `a`'s public
data, and its addresses of statics. -/
abbrev BG (D : Nat) (G H : Hash) (f : Fns) : State → State → Prop := BT S vO (PreT D G H f) (PubT G H)

theorem BG.bo {D : Nat} {G H : Hash} {f : Fns} {a t : State} (h : BG D G H f a t) : BO D a t :=
  let ⟨s, P, p, b, _⟩ := h; ⟨s, P.1, p.1, b⟩

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include cG hGh hGl hGv in
/-- `mgfXorT`, with its lengths and offsets the anchor's. -/
theorem mgf_any (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfAT S vO (PreT H.D G H f) (PubT G H) (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXorT f 9) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT S vO (PreT H.D G H f) (PubT G H) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ct (okT H.D G H f) hG cG x.2 hGh hGl hGv (tabT H.D G H f)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

/-- The checks passed, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 + (stackArg a 1).toNat ≤ (a.gpr .r6).toNat

theorem hk_of {D : Nat} {a s : State} (p : PubO a s) (h : HK D a) : 2 * D + 2 + mLen s ≤ kk s := by
  simp only [mLen, kk, p.args 1 (by decide), p.g .r6 (by decide)]; exact h

/-- `BG` with the checks passed. -/
def Bk (D : Nat) (G H : Hash) (f : Fns) (a t : State) : Prop := BG D G H f a t ∧ HK D a

theorem bk_pins {D : Nat} {α : Type} {Φ : α → State → Prop} (A : α → State) (h : ∀ x t, Φ x t → BO D (A x) t) :
    Pins Φ [] := fun x t₁ t₂ h₁ h₂ => ⟨((h x t₁ h₁).sp (oaepOk D)).trans ((h x t₂ h₂).sp (oaepOk D)).symm, fun _ h => nomatch h⟩

include cH cG hGh hGl hGv in
theorem encMain_ct : RelCT isa (Two fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms ∧
    HK H.D a) (encMain H f) fun _ _ => True := by
  obtain F := hfits hH
  obtain ⟨hE, _, _, _, _, _⟩ := offs
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  -- `EM` before masking.
  refine two_seq (Ψ := Bk H.D G H f) (encEm_taint H fun a t₁ t₂ ⟨s₁, _, ⟨p₁, _⟩, E₁, _⟩ ⟨s₂, _, ⟨p₂, _⟩, E₂, _⟩ => ?_)
    (fun a t ⟨s, P, p, E, sy, hk⟩ => WP.mono_syms (encEm_ok P.1 rfl hD0 hD64 E (hk_of p.1 hk)) fun t' ⟨b, _⟩ y =>
      ⟨⟨s, P, p, b, y.trans sy⟩, hk⟩) ?_
  · have f₁ := E₁.base.agree ((oaepOk H.D).agree p₁)
    obtain f₂ := E₂.base.agree ((oaepOk H.D).agree p₂)
    refine ⟨f₁.1.trans f₂.1.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [E₁.r9, E₂.r9, p₁.args 0 (by decide), p₂.args 0 (by decide)]
    · rw [E₁.r10, E₂.r10, p₁.args 1 (by decide), p₂.args 1 (by decide)]
    · rw [E₁.r11, E₂.r11, p₁.args 2 (by decide), p₂.args 2 (by decide)]
    · exact f₁.2.1.trans f₂.2.1.symm
    · exact (f₁.2.2 _ (by decide)).trans (f₂.2.2 _ (by decide)).symm
  -- The label's hash, through its table, and `lHash`.
  refine two_seq (Ψ := Bk H.D G H f) ((hashLabelT_ct (okT H.D G H f).s hH cH (tabL H.D G H f) (rl := .r19) (rn := .r20)
      (L := fun s => s.gpr .r9) (N := fun s => (s.gpr .r10).toNat) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun _ b => ⟨b.r19, by rw [b.r20, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩)
      (fun _ p => ⟨p.1.g _ (by decide), by rw [p.1.g .r10 (by decide)]⟩)
      (fun P => ⟨by rw [P.1.hrd]; simp, (P.1.ls.sub_right (sc_sub P.1)).sub_right (sc_in (by omega_arith)),
        (P.1.ls.sub_right (sc_sub P.1)).sub_right (sc_in (by omega_arith)), P.1.kl.sub_left (cR_sub _),
        BitVec.isLt _⟩)
      (fun h => lab2_taint h) (fun h => lab3_taint h)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁.1, h₂.1⟩) fun _ _ h => h)
    (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => WP.mono (hashLabelT_ok P.1 hH P.2.2 b sy) fun t' ⟨⟨b', _⟩, y⟩ =>
      ⟨⟨s, P, p, b', y⟩, hk⟩) ?_
  refine two_seq (Ψ := Bk H.D G H f) (copyLh_taint H (pins_of (oaepOk H.D) (fun _ _ h => h.1.bo) [.r14]))
    (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => WP.mono_syms (copyLh_ok P.1 hH rfl b) fun t' ⟨b', _⟩ y =>
      ⟨⟨s, P, p, b', y.trans sy⟩, hk⟩) ?_
  -- `DB` with MGF1 of the seed.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, (a.gpr .r6).toNat - H.D - 1)
  refine two_seq (Ψ := fun a t => (MgfAT S vO (PreT H.D G H f) (PubT G H) (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => ?_) ?_
  · have k2 := P.1.k2
    obtain ek : (a.gpr .r6).toNat = (s.gpr .r6).toNat := by rw [p.1.g .r6 (by decide)]
    refine WP.of_syms (wp_addi (h := by omega_arith) fun t₁ o₁ e₁ => wp_li (by omega_arith) fun t₂ o₂ e₂ =>
      wp_addi (h := by omega_arith) fun t₃ o₃ e₃ => wp_subi (h := by omega_arith) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
    obtain k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfAT S vO (PreT H.D G H f) (PubT G H) 1 H.D (1 + H.D) ((a.gpr .r6).toNat - H.D - 1) a t₄ ∧
      MFit 1 H.D (1 + H.D) ((a.gpr .r6).toNat - H.D - 1)) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.1.fits k₄, y.trans sy, ?_, ?_, ?_, ?_⟩, ⟨by omega_using [hD64], by omega_using [hD64, k2, ek], .inl (by omega_using []), by omega⟩⟩, hk⟩
    · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, b.r14, p.1.S, hE]
    · rw [o₄.get .r25, o₃.get .r25, e₂]
    · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, b.r14, p.1.S, hE, Nat.zero_add]
    · rw [e₄, o₃.get .r15, o₂.get .r15, o₁.get .r15, b.r15, sub_k (by omega)]; congr 1; omega_using [ek]
  refine two_seq (Ψ := Bk H.D G H f) ((mgf_any hG cG hGh hGl hGv q₁).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨⟨s, P, p, b, sy, h24, h25, h26, h27⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXorT_ok P.1.fits hG P.2.1 hGh hGl hGv hf b sy (by rw [h24, p.1.S]) h25 (by rw [h26, p.1.S]) h27)
      fun t' ⟨⟨b', _⟩, y⟩ => ⟨⟨s, P, p, b', y⟩, hk⟩) ?_
  -- The seed with MGF1 of `maskedDB`.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, (a.gpr .r6).toNat - H.D - 1, 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfAT S vO (PreT H.D G H f) (PubT G H) (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => ?_) ?_
  · have k2 := P.1.k2
    obtain ek : (a.gpr .r6).toNat = (s.gpr .r6).toNat := by rw [p.1.g .r6 (by decide)]
    refine WP.of_syms (wp_addi (h := by omega_arith) fun t₁ o₁ e₁ => wp_subi (h := by omega_arith) fun t₂ o₂ e₂ =>
      wp_addi (h := by omega_arith) fun t₃ o₃ e₃ => wp_li (by omega_arith) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
    obtain k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfAT S vO (PreT H.D G H f) (PubT G H) (1 + H.D) ((a.gpr .r6).toNat - H.D - 1) 1 H.D a t₄ ∧
      MFit (1 + H.D) ((a.gpr .r6).toNat - H.D - 1) 1 H.D) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.1.fits k₄, y.trans sy, ?_, ?_, ?_, ?_⟩, ⟨by omega_arith, by omega_arith, .inr (by omega_arith), by omega_arith⟩⟩, hk⟩
    · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, b.r14, p.1.S, hE, Nat.zero_add]
    · rw [o₄.get .r25, o₃.get .r25, e₂, o₁.get .r15, b.r15, sub_k (by omega)]; congr 1; omega_using [ek]
    · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, b.r14, p.1.S, hE]
    · rw [e₄]
  refine two_seq (Ψ := Bk H.D G H f) ((mgf_any hG cG hGh hGl hGv q₂).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨⟨s, P, p, b, sy, h24, h25, h26, h27⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXorT_ok P.1.fits hG P.2.1 hGh hGl hGv hf b sy (by rw [h24, p.1.S]) h25 (by rw [h26, p.1.S]) h27)
      fun t' ⟨⟨b', _⟩, y⟩ => ⟨⟨s, P, p, b', y⟩, hk⟩) ?_
  -- The public-key operation.
  exact two_seq (pubArgs_taint (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, _⟩, _⟩ =>
    WP.mono (pubArgs_ok P.1 b rfl) fun t' h => ⟨s, P.1, p.1, _, h⟩) call_ct

include cH cG hGh hGl hGv in
theorem checks_ct : RelCT isa (Two fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms)
    (checks H f) fun _ _ => True := by
  have hD64 := hH.hD64
  let K := fun (a : State) => (a.gpr .r6).toNat
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms ∧
      (t.gpr .r3 != 0) = decide (K a < 2 * H.D + 2))
    (chkK_taint H (bk_pins id fun _ _ ⟨s, P, p, E, _⟩ => ⟨s, P.1, p.1, E.base⟩)) (fun a t ⟨s, P, p, E, sy⟩ => ?_) ?_
  · have k2 := P.1.k2
    obtain ka : (a.gpr .r6).toNat ≤ 1024 := by rw [← p.1.g .r6 (by decide)]; exact P.1.k2
    refine WP.of_syms (wp_li (by omega_arith) fun t₁ o₁ e₁ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_sub fun t₂ o₂ e₂ =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_lsr fun t₃ o₃ e₃ => wp_nil fun y => ?_)
    obtain k₃ : Only [.r3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    refine ⟨s, P, p, entered_only P.1 E k₃, y.trans sy, ?_⟩
    rw [e₃, e₂, e₁, o₁.get .r15, E.base.r15, ← ofNat_toNat (s.gpr .r6), p.1.g .r6 (by decide)]
    exact ne_zero_ltBit (by omega_arith) (by omega_arith)
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, _, c₁⟩ ⟨_, _, _, _, _, c₂⟩ => by rw [eval_nonzero, eval_nonzero, c₁, c₂])
    (fail_taint (pins_of (oaepOk H.D) (fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P.1, p.1, E.base⟩) [.r15, .r16])) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms ∧
      2 * H.D + 2 ≤ K a ∧ (t.gpr .r3 != 0) = decide (K a - (2 * H.D + 2) < (stackArg a 1).toNat))
    (chkMsg_taint H (bk_pins id fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P.1, p.1, E.base⟩))
    (fun a t ⟨⟨s, P, p, E, sy, c⟩, hc⟩ => ?_) ?_
  · have k2 := P.1.k2
    obtain hk : 2 * H.D + 2 ≤ K a := by rw [eval_nonzero, c] at hc; simpa using hc
    obtain ek : K a = (s.gpr .r6).toNat := by simp only [K]; rw [p.1.g .r6 (by decide)]
    refine WP.of_syms (wp_li (by omega_arith) fun t₄ o₄ e₄ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_sub fun t₅ o₅ e₅ =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_sub fun t₆ o₆ e₆ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_lsr fun t₇ o₇ e₇ =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_lsr fun t₈ o₈ e₈ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_or fun t₉ o₉ e₉ =>
      wp_nil fun y => ?_)
    obtain k₉ : Only [.r3, .r4] t t₉ := (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉))))).mono
    refine ⟨s, P, p, entered_only P.1 E k₉, y.trans sy, hk, ?_⟩
    rw [e₉, e₈, o₇.get .r10, o₆.get .r10, o₅.get .r10, o₄.get .r10, E.r10, o₈.get .r4, e₇, e₆,
      o₅.get .r10, o₄.get .r10, E.r10, e₅, o₄.get .r15, E.base.r15, e₄,
      ← ofNat_toNat (s.gpr .r6), ← ofNat_toNat (stackArg s 1), Offset.ofNat_sub_ofNat (by omega_arith),
      p.1.args 1 (by decide), ← ek]
    exact msgBit (by omega_arith) (stackArg a 1).isLt
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, _, _, c₁⟩ ⟨_, _, _, _, _, _, c₂⟩ => by
      rw [eval_nonzero, eval_nonzero, c₁, c₂])
    (fail_taint (pins_of (oaepOk H.D) (fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P.1, p.1, E.base⟩) [.r15, .r16])) ?_
  refine (encMain_ct hH cH hG cG hGh hGl hGv).mono (fun _ _ h => ?_) fun _ _ h => h
  obtain ⟨a, ⟨⟨s₁, P₁, p₁, E₁, y₁, hk, c₁⟩, h₁⟩, ⟨⟨s₂, P₂, p₂, E₂, y₂, -, -⟩, -⟩⟩ := h
  rw [eval_nonzero, c₁] at h₁
  have : ¬ (K a - (2 * H.D + 2) < (stackArg a 1).toNat) := by simpa using h₁
  obtain hK : HK H.D a := by simp only [HK, K] at *; omega_arith
  exact ⟨a, ⟨s₁, P₁, p₁, E₁, y₁, hK⟩, ⟨s₂, P₂, p₂, E₂, y₂, hK⟩⟩

variable {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)

include cH cG hGh hGl hGv hHh hHl in
theorem code_ct (hl : H.D ∈ lens) :
    RelCT isa (Two fun a s => PreT H.D G H f s ∧ PubT G H a s) (encrypt f) fun _ _ => True := by
  have hD64 := hH.hD64
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.2.1.sp.trans h₂.2.1.sp.symm, fun _ h => nomatch h⟩) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.1.sp,
      h₂.2.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by subst e; exact WP.mono_syms (entry_ok P.1) fun t E y => ⟨s, P, p, E, y⟩) ?_
  -- The label's hash function's digest length to `r3`.
  let E₃ := fun (a : State) (t : State) => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms ∧
    t.gpr .r3 = BitVec.ofNat 64 H.D
  obtain hlen : RelCT isa (Two fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms)
      (.block (lenLoad 8)) (Two E₃) := (tword_two (okT H.D G H f).s (tabL H.D G H f)
      (Φ := fun (ac : State × Nat) t => ∃ s, PreT H.D G H f s ∧ PubT G H ac.1 s ∧ Entered s t ∧ t.syms = s.syms)
      (fun _ _ ⟨s, P, p, E, y⟩ => ⟨s, P, p, E.base, y⟩) (d := .r3) (.inr (.inr rfl)) (k := 6) (by decide)
      (v := fun _ => BitVec.ofNat 64 H.D) fun P _ => P.2.2.d).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁, h₂⟩)
      fun _ _ ⟨ac, ⟨t₁, ⟨s₁, P₁, p₁, E₁, y₁⟩, o₁, z₁, e₁⟩, ⟨t₂, ⟨s₂, P₂, p₂, E₂, y₂⟩, o₂, z₂, e₂⟩⟩ =>
        ⟨ac.1, ⟨s₁, P₁, p₁, entered_only P₁.1 E₁ o₁, z₁.trans y₁, e₁⟩, ⟨s₂, P₂, p₂, entered_only P₂.1 E₂ o₂,
          z₂.trans y₂, e₂⟩⟩
  refine RelCT.seq hlen ?_
  -- The code for that length.
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Saves s t)
    (byLen_ct (D := H.D) (Φ := E₃) (by omega_using [hD64]) (fun _ _ ⟨_, _, _, _, _, h3⟩ => h3)
      (fun _ t₁ t₂ ⟨_, P₁, p₁, E₁, _⟩ ⟨_, P₂, p₂, E₂, _⟩ =>
        (E₁.base.agree ((oaepOk H.D).agree p₁.1)).1.trans (E₂.base.agree ((oaepOk H.D).agree p₂.1)).1.symm)
      (fun _ _ _ ⟨s, P, p, E, y, h3⟩ o y' => ⟨s, P, p, entered_only P.1 E o, y'.trans y, by rw [o.get .r3]; exact h3⟩)
      ?_ hl lens_certs)
    fun a t ⟨s, P, p, E, y, h3⟩ => ?_) ?_
  · rw [checks_D (G := ofLen H.D) (G' := H) rfl]
    exact (checks_ct hH cH hG cG hGh hGl hGv).mono (fun _ _ ⟨a, ⟨s₁, P₁, p₁, E₁, y₁, _⟩, ⟨s₂, P₂, p₂, E₂, y₂, _⟩⟩ =>
      ⟨a, ⟨s₁, P₁, p₁, E₁, y₁⟩, ⟨s₂, P₂, p₂, E₂, y₂⟩⟩) fun _ _ h => h
  · refine byLen_ok (D := H.D) (by omega_using [hD64])
      (F := fun u => Entered s u ∧ u.syms = s.syms ∧ u.gpr .r3 = BitVec.ofNat 64 H.D)
      (fun _ h => h.2.2) (fun u u' ⟨E', y', r3'⟩ o y => ⟨entered_only P.1 E' o, y.trans y',
        by rw [o.get .r3]; exact r3'⟩) ?_ hl (fun x hx => (lens_certs x hx).1) t ⟨E, y, h3⟩
    intro u ⟨E', y', _⟩
    rw [checks_D (G := ofLen H.D) (G' := H) rfl]
    exact WP.mono (checks_done hH hG hHh hHl hGh hGl hGv P.1 P.2.1 P.2.2 E' y') fun t' d => ⟨s, P, p, d.1⟩
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.sp, p₂.1.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaOaep.PPC64LE

end

end


/-!
# RSAES-OAEP encryption on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. The shared contract's public
data as `PubO`, with the tables' (`pubT_of`); constant time
(`code_constantTime`, from `code_ct`); states meeting the precondition, with
both tables that of any `w` of `vs`, at `0x300000` (`enc_sat`); and
`enc_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.MdHashTable.PPC64LE (MVar tables fns3 Coh)

theorem leak_eq {a b c d : List Byte} {w w' : List (BitVec 64)} (ha : a.length = c.length)
    (hb : b.length = d.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (c ++ d).map (·.toNat) ++ w'.map (·.toNat)) :
    b = d ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  obtain hi : a ++ b = c ++ d := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  exact ⟨(List.append_inj hi ha).2, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

/-- The contract's public data: `PubO`, the tables at the same addresses,
the tables' functions at the same addresses, and the same tables held. -/
theorem pubT_of {ts : List FnTable} {s₁ s₂ : State} (h : (encSpec ts).pub s₁ s₂) :
    PubO s₁ s₂ ∧ stackArg s₂ 9 = stackArg s₁ 9 ∧ stackArg s₂ 8 = stackArg s₁ 8 ∧
      (∀ f ∈ (ts.map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 8) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 8) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 9) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 9) (FnTable.words isa s₂ T)) := by
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold encSpec at h
  rw [e] at h
  sig_pub [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_ten, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htabL, htab, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  obtain ⟨he, hw⟩ := leak_eq (by simp [bytesAt_length, h6]) (by simp [bytesAt_length, h8]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, he.symm, hw.symm⟩, a9.symm, a8.symm,
    fun f hf => hsy f (List.mem_append_left _ hf), fun T hT => htabL _ _ rfl rfl T hT, fun T hT => htab _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm]

theorem pubO_refl (s : State) : PubO s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- Constant time: the tables of the first run, which the public data makes
the second's, at the same addresses with their functions at the same
addresses. -/
theorem code_constantTime {vs : List MVar} (hc : Coh vs) :
    ConstantTime isa (encSpec (tables vs)).pre (encSpec (tables vs)).pub (encrypt (fns3 vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, hpw₁⟩ := spec_tab h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, a9, a8, hsy, hiffL, hiff⟩ := pubT_of hp
  obtain hhL₂ := (hiffL _ hT₁).mp hhL₁
  obtain hh₂ := (hiff _ hT).mp hh₁
  obtain hpw₂ := (spec_tab h₂).2.2
  obtain hn := Proof.MdHashTable.PPC64LE.mem_names hw
  obtain hnL := Proof.MdHashTable.PPC64LE.mem_names hw₁
  obtain hH₁ := Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hhL₁).2.2.2
  obtain hH₂ := Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hhL₂).2.2.2
  obtain P₁ : PreO w₁.H.D s₁ := w₁.l.len ▸ preO_of h₁ hH₁
  obtain P₂ : PreO w₁.H.D s₂ := w₁.l.len ▸ preO_of h₂ hH₂
  obtain q₁ := hpw₁.sublist (List.sublist_append_left _ _)
  obtain q₂ := hpw₂.sublist (List.sublist_append_left _ _)
  exact code_ct w₁.l.ok w₁.l.ct w.l.ok w.l.ct w.l.hash w.l.len w.l.valid w₁.l.hash w₁.l.len w₁.l.lens_mem
    _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entry hc P₁ q₁ hw hh₁, tabS_entryL hc P₁ q₁ hw₁ hhL₁⟩, pubO_refl s₁, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩,
      ⟨P₂, tabS_entry hc P₂ q₂ hw hh₂, tabS_entryL hc P₂ q₂ hw₁ hhL₂⟩, p, a9, (hsy _ hn.1).symm,
      (hsy _ hn.2.1).symm, (hsy _ hn.2.2.1).symm, a8, (hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm,
      (hsy _ hnL.2.2.1).symm⟩ e₁ e₂

/-- `vg_rsa_oaep_encrypt_precomputed` against its contract, for the tables
of `vs`, given a state meeting it. -/
theorem enc_verified {vs : List MVar} (hc : Coh vs) (hsat : ∃ s, (encSpec (tables vs)).pre s) :
    Verified PPC64LE.target (encrypt (fns3 vs)) (encSpec (tables vs)) :=
  ⟨code_correct hc, code_constantTime hc, hsat⟩

/-! ## A state meeting the precondition -/

/-- A state meeting encryption's contract for a seed of `D` bytes, but for
the tables: a 512-bit modulus, a one-byte `e`, an empty label and message,
the seed, a working space of 2080 words, 16 words of `pre` at `0x5000`, the
stack arguments at `sp + 96`, and both tables' address `0x300000`. -/
def encSatState (D : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10061 then 0x41
    else bif Nat.beq a.toNat 0x10071 then 0x42 else bif Nat.beq a.toNat 0x10078 then BitVec.ofNat 8 D
    else bif Nat.beq a.toNat 0x10082 then 0x02
    else bif Nat.beq a.toNat 0x10088 then 0x20 else bif Nat.beq a.toNat 0x10089 then 0x08
    else bif Nat.beq a.toNat 0x10091 then 0x50 else bif Nat.beq a.toNat 0x10098 then 16
    else bif Nat.beq a.toNat 0x100A2 then 0x30 else bif Nat.beq a.toNat 0x100AA then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, D⟩, ⟨0x5000, 128⟩, ⟨0x300000, 88⟩,
    ⟨0x300000, 88⟩, ⟨0x10060, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List MVar} {w : MVar}

theorem stackArgAddr_sat (D j : Nat) (hj : j < 10) :
    (stackArgAddr (encSatState D) j).toNat + 8 ≤ 0x300000 := by
  revert j; show ∀ j < 10, (stackArgAddr (encSatState 0) j).toNat + 8 ≤ 0x300000; decide

theorem sat_a0 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 0 = 0x4100 :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 0 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 0 = 0x4100 by decide) D hD)
theorem sat_a1 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 1 = 0 :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 1 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 1 = 0 by decide) D hD)
theorem sat_a2 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 2 = 0x4200 :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 2 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 2 = 0x4200 by decide) D hD)
theorem sat_a3 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 3 = BitVec.ofNat 64 D :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 3 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 3 = BitVec.ofNat 64 D by decide) D hD)
theorem sat_a4 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 4 = 0x20000 :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 4 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 4 = 0x20000 by decide) D hD)
theorem sat_a5 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 5 = 2080 :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 5 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 5 = 2080 by decide) D hD)
theorem sat_a6 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 6 = 0x5000 :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 6 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 6 = 0x5000 by decide) D hD)
theorem sat_a7 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 7 = 16 :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 7 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 7 = 16 by decide) D hD)
theorem sat_a8 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 8 = 0x300000 :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 8 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 8 = 0x300000 by decide) D hD)
theorem sat_a9 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 9 = 0x300000 :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 9 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 9 = 0x300000 by decide) D hD)
theorem sat_e (D : Nat) : stackArgAddr (Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w) 0 = 0x10060 :=
  show stackArgAddr (encSatState 0) 0 = _ by decide

/-- A state meeting the contract, with both tables that of `w`, at
`0x300000`. -/
theorem enc_sat (hw : w ∈ vs) (hl : (Proof.MdHashTable.PPC64LE.names vs).length < 2 ^ 32) :
    ∃ s, (encSpec (tables vs)).pre s := by
  obtain hha : ∀ s : State, Spec.MdHashTable.hashAt 64 (Proof.MdHashTable.PPC64LE.withTable s vs w).mem 0x300000 =
      some w.l.G := fun s => Proof.MdHashTable.PPC64LE.hashAt_tableOf
        (Proof.MdHashTable.PPC64LE.held_tableOf (Proof.MdHashTable.PPC64LE.withTable_held s vs w)).2.2.2
  obtain hl' : w.l.G.len ∈ Impl.RsaOaep.PPC64LE.lens := w.l.len ▸ w.l.lens_mem
  generalize hDd : w.l.G.len = D at hl'
  refine ⟨Proof.MdHashTable.PPC64LE.withTable (encSatState D) vs w, ?_⟩
  have e304 : (304 : Nat) = 303 + 1 := rfl
  obtain hha' := hha (encSatState D)
  obtain a0 := sat_a0 (vs := vs) (w := w) hl'
  obtain a1 := sat_a1 (vs := vs) (w := w) hl'
  obtain a2 := sat_a2 (vs := vs) (w := w) hl'
  obtain a3 := sat_a3 (vs := vs) (w := w) hl'
  obtain a4 := sat_a4 (vs := vs) (w := w) hl'
  obtain a5 := sat_a5 (vs := vs) (w := w) hl'
  obtain a6 := sat_a6 (vs := vs) (w := w) hl'
  obtain a7 := sat_a7 (vs := vs) (w := w) hl'
  obtain a8 := sat_a8 (vs := vs) (w := w) hl'
  obtain a9 := sat_a9 (vs := vs) (w := w) hl'
  unfold encSpec
  rw [e304]
  simp only [Impl.RsaOaep.PPC64LE.lens, List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
      argRegs, stackArgs_ten, List.append_eq, List.range, List.range.loop]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, sat_e]
    sig_and_intros
    all_goals first
      | exact ⟨Proof.MdHashTable.PPC64LE.tableOf w, List.mem_map_of_mem hw, Proof.MdHashTable.PPC64LE.held_twL _ _ _ rfl⟩
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | (intro H' hH'
         obtain rfl := Option.some.inj (hha'.symm.trans hH')
         rw [hDd]; rfl)
      | exact Proof.HashTable.symsOf_distinct2 hl
      | (simp only [Spec.Rsa.lenValid]; decide)

end

end VG.Proof.RsaOaep.PPC64LE

end

end


/-!
# RSAES-OAEP on PPC64LE: the instances emitted

Untrusted: everything here is checked by Lean. What the registration checks
of the hash functions whose tables a function takes (`OK`), and the
instances' proofs against the contracts it states: encryption (`enc_ok`)
and decryption (`dec_ok`, and with the key's precomputed values `decP_ok`), with both hash functions any of `vs`' tables.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE
open VG.Proof.MdHashTable.PPC64LE (MVar tables names Coh fns3)

/-- What the registration checks of the hash functions whose tables a
function takes: their functions of the same name have the same code, there
are not too many to give distinct addresses in the witnesses, and there is
one. -/
def OK (vs : List MVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ []

instance (vs : List MVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem OK.mem {vs : List MVar} (h : OK vs) : ∃ w, w ∈ vs := List.exists_mem_of_ne_nil _ h.2.2

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs`. -/
theorem enc_ok (vs : List MVar) (hok : OK vs) :
    Verified PPC64LE.target (Impl.RsaOaep.PPC64LE.encrypt (fns3 vs)) (encSpec (tables vs)) :=
  enc_verified hok.1 (let ⟨_, hw⟩ := hok.mem; enc_sat hw hok.2.1)

/-- `vg_rsa_oaep_decrypt`, with the tables of `vs`. -/
theorem dec_ok (vs : List MVar) (hok : OK vs) :
    Verified PPC64LE.target (Impl.RsaOaep.PPC64LE.Dec.decrypt (fns3 vs)) (Dec.decSpec (tables vs)) :=
  Dec.dec_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_sat hw hok.2.1)

/-- `vg_rsa_oaep_decrypt_precomputed`, with the tables of `vs`. -/
theorem decP_ok (vs : List MVar) (hok : OK vs) :
    Verified PPC64LE.target (Impl.RsaOaep.PPC64LE.Dec.decryptP (fns3 vs)) (Dec.decSpecP (tables vs)) :=
  Dec.decP_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.decP_sat hw hok.2.1)

end VG.Proof.RsaOaep.PPC64LE
