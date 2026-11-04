module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.MComp
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.MPad
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Hash
public import VerifiedGarbage.Proof.Pbkdf2.MdStep
public import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Select
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSASSA-PSS verification on PPC64LE: `ctHash`

Untrusted: everything here is checked by Lean. What `ctHash` needs of the
hash function's Merkle–Damgård code (`CtOK`: its sizes, its length field's
code, its compression function and its digest); `compLoop_ok`: every block
of `M'` compressed into the hash value at `oSt`, the hash value after block
`fb` selected at `oSel`; and `ctHash_ok`: from `M'` of `ℓ` bytes at `oY`
followed by zeros, its digest at `oDig`, by `Proof.RsaPss.pad_getD`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.MdStream.PPC64LE (Params lg)
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa tcall)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.MdHashTable.PPC64LE (digestK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 view_wb sc_in sc_inR sc_inW sc_cov sdis cR_dis Same)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_xor wp_and wp_lsr wp_lsl
  wp_lbz wp_stb wp_nil wp_countdown)
open VG.Proof.Mgf1 (ifp ifn)

/-- What `ctHash` needs of a hash function's Merkle–Damgård code: its
sizes, its length field (`P.len`), its compression function `cc` and the
digest `dc` of its hash value. -/
structure CtOK (P : Params) (md : Md P.B P.N P.L) (cc dc : Prog isa) : Prop where
  dims : Dims P
  shape : ShapeD md P.N
  lenLr : (instrs (.block P.len : Prog isa)).all (fun i => !i.writesLr) = true
  callee : CalleeOk md cc
  dig : ∀ u, (digestK md).pre u → ∃ t u', Exec isa dc u t u' ∧ abiPreserved u u' ∧ (digestK md).post u u'
  digNF : dc.noFrames = true
  reloc : md.Reloc
  lenOk : ∀ n < 2 ^ 32, md.lenOk n

theorem off_add' (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := off_off p a b

/-- The bytes of `M'`'s place, from the view `V`. -/
def yl (V : Nat → Byte) : List Byte := (List.range 2048).map fun k => V (oY + k)

theorem yl_getD {V : Nat → Byte} {k : Nat} (hk : k < 2048) : (yl V).getD k 0 = V (oY + k) := by
  simp only [yl, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some]

/-- What the compression loop keeps after `i` blocks, from the state `t`. -/
structure CompI (D : Nat) (s : State) {P : Params} (md : Md P.B P.N P.L) (fb : Nat) (hv : md.HV) (t : State)
    (i : Nat) (u : State) : Prop where
  base : Base Sp (vP D) s u
  sy : u.syms = s.syms
  keep : ∀ r ∈ [Reg.r24, .r27], u.gpr r = t.gpr r
  r26 : u.gpr .r26 = BitVec.ofNat 64 i
  st : md.stateAt u.mem (off (Sp s) oSt) = md.compressList hv (yl (view t.mem (Sp s))) i
  sel : fb < i → md.stateAt u.mem (off (Sp s) oSel) = md.compressList hv (yl (view t.mem (Sp s))) (fb + 1)
  mem : ∀ o < oRsa, (o < oSt ∨ oY ≤ o ∧ o < oY + 2048) → view u.mem (Sp s) o = view t.mem (Sp s) o

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash}
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} {j : Nat} {p : Addr} (T : MdTabS H cn cc dn dc f j Sp s p)
  {P : Params} {md : Md P.B P.N P.L} (ok : CtOK P md cc dc)
include L T ok

/-- `compLoop`, with `nbm` in `r28` and the last block's index `fb` in
`r27`. -/
theorem compLoop_ok {t : State} (h : Base Sp (vP D) s t) (sy : t.syms = s.syms) {nbm fb : Nat}
    (h28 : t.gpr .r28 = BitVec.ofNat 64 nbm) (h27 : t.gpr .r27 = BitVec.ofNat 64 fb) (hn0 : 0 < nbm)
    (hnb : nbm * P.B ≤ 2048) (hfb : fb < nbm) :
    WP isa (compLoop P f j) t fun t' => CompI D s md fb (md.stateAt t.mem (off (Sp s) oSt)) t nbm t' := by
  have F := L.F
  have hR : oRsa = 8192 := rfl
  have hY : oY = 2560 := rfl
  have hSt : oSt = 1024 := rfl
  have hSl : oSel = 4800 := rfl
  have hW : oW = 1352 := rfl
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  have hN := ok.dims.N
  have hso := ok.dims.so
  have hB := ok.dims.B
  have hn : nbm ≤ 32 := by rcases hB with e | e <;> rw [e] at hnb <;> omega
  let V := view t.mem (Sp s)
  let hv := md.stateAt t.mem (off (Sp s) oSt)
  refine WP.seq (WP.of_syms (wp_li (by decide) fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_))
  refine wp_countdown (cnt := .r28) (N := nbm) (by omega) hn0 (CompI D s md fb hv t) ?_
    ⟨h.only F o₁, y₁.trans sy, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> exact o₁.get _,
      e₁, by rw [o₁.mem, Md.compressList_zero], fun h => absurd h (Nat.not_lt_zero _), fun o _ _ => by rw [o₁.mem]⟩
    (by rw [o₁.get .r28, h28])
  intro i hi u I _
  have hBi : P.B * i + P.B ≤ 2048 := by
    rw [← Nat.mul_succ]; exact Nat.le_trans (Nat.mul_le_mul_left _ hi) (by rw [Nat.mul_comm]; exact hnb)
  -- The arguments.
  refine WP.seq (WP.of_syms (wp_addi (h := by decide) fun u₁ p₁ f₁ => wp_lsl (h := by omega) fun u₂ p₂ f₂ =>
    wp_add fun u₃ p₃ f₃ => wp_addi (h := by decide) fun u₄ p₄ f₄ => wp_li (by decide) fun u₅ p₅ f₅ =>
    wp_addi (h := by decide) fun u₆ p₆ f₆ => wp_nil fun y₆ => ?_))
  have k₆ : Only [.r3, .r4, .r5, .r6] u u₆ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans p₆))))).mono
  have b₆ := I.base.only F k₆
  have g4 : u₆.gpr .r4 = off (Sp s) (oY + P.B * i) := by
    rw [p₆.get .r4, p₅.get .r4, f₄, f₃, f₂, p₁.get .r26, I.r26, p₂.get .r14, p₁.get .r14, I.base.r14,
      ofNat_shl (by rw [hlg]; omega), hlg]
    show _ = Sp s + _
    rw [BitVec.add_comm (BitVec.ofNat 64 _) (Sp s), BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega
  -- The compression.
  refine WP.seq (WP.mono (compM_ok F T ok.callee hN.2 hso.2 b₆ (y₆.trans I.sy) (b := P.B * i)
      (by rw [p₆.get .r3, p₅.get .r3, p₄.get .r3, p₃.get .r3, p₂.get .r3, f₁, I.base.r14])
      g4 (by rw [p₆.get .r5, f₅]) (by rw [f₆, p₅.get .r14, p₄.get .r14, p₃.get .r14, p₂.get .r14, p₁.get .r14,
        I.base.r14]) (by omega)) fun u₇ ⟨⟨b₇, g₇, s₇, st₇⟩, y₇⟩ => ?_)
  -- The selection.
  have r26₇ : u₇.gpr .r26 = BitVec.ofNat 64 i := by rw [g₇ _ (by decide), k₆.get .r26, I.r26]
  have r27₇ : u₇.gpr .r27 = BitVec.ofNat 64 fb := by rw [g₇ _ (by decide), k₆.get .r27, I.keep .r27 (by simp), h27]
  refine WP.seq (WP.of_syms (WP.mono (selHash_ok L hN.1 hN.2 b₇ r26₇ r27₇ (by omega) (by omega))
    fun u₈ ⟨b₈, k₈, v₈⟩ y₈ => ?_))
  refine WP.of_syms (wp_addi fun u₉ p₉ f₉ => wp_subi fun u₁₀ p₁₀ f₁₀ => wp_nil fun y₁₀ => ?_)
  have k₁₀ : Only [.r26, .r28] u₈ u₁₀ := (p₉.trans p₁₀).mono
  have m₁₀ : u₁₀.mem = u₈.mem := k₁₀.mem
  -- The bytes of the hash value at `oSt` are kept by the selection.
  have vSt : ∀ k < P.N, u₁₀.mem (off (Sp s) oSt + BitVec.ofNat 64 k) = u₇.mem (off (Sp s) oSt + BitVec.ofNat 64 k) :=
    fun k hk => by
      have := v₈ (oSt + k) (by omega); rw [ifn (by omega)] at this
      rw [m₁₀, off_add']; exact this
  have hblk : md.blockAt u.mem (off (Sp s) (oY + P.B * i)) = md.blockOf (yl V) i := by
    simp only [Md.blockAt, Md.blockOf]
    refine md.parse_congr fun k hk => ?_
    rw [yl_getD (by omega), off_add', show oY + P.B * i + k = oY + (P.B * i + k) by omega]
    exact I.mem _ (by omega) (.inr ⟨by omega, by omega⟩)
  have hst : md.stateAt u₁₀.mem (off (Sp s) oSt) = md.compressList hv (yl V) (i + 1) := by
    rw [md.stateAt_congr vSt, st₇, k₆.mem, hblk, I.st, Md.compressList_succ]
  refine ⟨⟨b₈.only F k₁₀, y₁₀.trans (y₈.trans y₇), fun r hr => ?_, ?_, hst, fun hlt => ?_, fun o ho hr => ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [k₁₀.get .r24, k₈.get .r24, g₇ _ (by decide), k₆.get .r24, I.keep .r24 (by simp)]
    · rw [k₁₀.get .r27, k₈.get .r27, r27₇, h27]
  · rw [p₁₀.get .r26, f₉, k₈.get .r26, r26₇, BitVec.ofNat_add_ofNat]
  · by_cases e : i = fb
    · subst e
      rw [← hst]
      refine ok.reloc _ _ _ _ fun k hk => ?_
      have := v₈ (oSel + k) (by omega)
      rw [ifp ⟨by omega, by omega, rfl⟩, show oSt + (oSel + k - oSel) = oSt + k by omega] at this
      have a1 : u₁₀.mem (off (Sp s) oSel + BitVec.ofNat 64 k) = u₇.mem (off (Sp s) oSt + BitVec.ofNat 64 k) := by
        rw [m₁₀, off_add', off_add']; exact this
      exact a1.trans (vSt k hk).symm
    · have hlt' : fb < i := by omega
      rw [← I.sel hlt']
      refine md.stateAt_congr fun k hk => ?_
      have e8 := v₈ (oSel + k) (by omega)
      rw [ifn (fun h => e h.2.2)] at e8
      have e7 := s₇ (oSel + k) (by omega) (by simp; omega)
      rw [m₁₀, off_add']; exact e8.trans (e7.trans (by rw [k₆.mem]; rfl))
  · have e8 := v₈ o ho
    rw [ifn (by omega)] at e8
    have e7 := s₇ o ho (by simp; omega)
    rw [m₁₀]; exact e8.trans (e7.trans (by rw [k₆.mem]; exact I.mem o ho hr))
  · rw [f₁₀, p₉.get .r28, k₈.get .r28, g₇ _ (by decide), k₆.get .r28]

end


open VG.Proof.RsaPss (lastBlk padded)

theorem or0 (x : Byte) : x ||| 0 = x := BitVec.or_zero
theorem zor (x : Byte) : 0 ||| x = x := BitVec.zero_or

/-- Bytes before `M'`'s place are as in `V`. -/
theorem vLen_lt (V : Nat → Byte) (len : List Byte) (B L fb : Nat) :
    ∀ n o, o < oY → vLen V len B L fb n o = V o
  | 0, _, _ => rfl
  | n + 1, o, h => by
    simp only [vLen]
    rw [ifn (by omega), vLen_lt V len B L fb n o h]

/-- `M'` after its `0x80` and its length field: the padded message, over
its first `fb + 1` blocks. -/
theorem y_pad {B L fb nbm : Nat} (msg len : List Byte) (hfb : fb = lastBlk B L msg.length) (hLB : L < B)
    (hfbn : fb < nbm) (W : Nat → Byte)
    (hW : ∀ j < B * nbm, W (oY + j) = msg.getD j 0 ||| (if j = msg.length then 0x80 else 0)) :
    ∀ j < B * (fb + 1), vLen W len B L fb nbm (oY + j) = padded B L msg len j := by
  intro j hj
  have hB0 : 0 < B := by omega
  have e := Nat.div_add_mod j B
  have hk : j % B < B := Nat.mod_lt _ hB0
  have hb : j / B < fb + 1 := (Nat.div_lt_iff_lt_mul hB0).mpr (by rw [Nat.mul_comm]; exact hj)
  have hfit : msg.length + L < B * (fb + 1) := by
    rw [hfb]; unfold lastBlk
    have := Nat.lt_div_mul_add (a := msg.length + L) (b := B) hB0
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]; omega
  have hlow : B * fb ≤ msg.length + L := by rw [hfb]; unfold lastBlk; exact Nat.mul_div_le _ _
  have hjn : j < B * nbm := Nat.lt_of_lt_of_le hj (Nat.mul_le_mul_left _ hfbn)
  generalize hbv : j / B = b at e hb
  generalize hkv : j % B = k at e hk
  subst e
  rw [show oY + (B * b + k) = oY + B * b + k by omega, vLen_at W len fb (Nat.le_of_lt hLB) nbm (by omega) hk,
    show oY + B * b + k = oY + (B * b + k) by omega, hW _ hjn]
  simp only [padded, ← hfb]
  rw [Nat.mul_add, Nat.mul_one] at hfit hj
  have hz : ∀ i, msg.length ≤ i → msg.getD i 0 = 0 := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]; rfl
  by_cases e₁ : B * b + k < msg.length
  · have : ¬(b = fb ∧ B - L ≤ k) := by
      rintro ⟨rfl, _⟩; omega
    rw [ifn (by omega), ifn this, ifp e₁, or0, or0]
  · rw [hz _ (by omega), ifn e₁]
    by_cases e₂ : B * b + k = msg.length
    · have : ¬(b = fb ∧ B - L ≤ k) := by
        rintro ⟨rfl, _⟩; omega
      rw [ifp e₂, ifn this, ifp e₂, or0, zor]
    · rw [ifn e₂, ifn e₂]
      by_cases e₃ : b = fb
      · subst e₃
        by_cases e₄ : B - L ≤ k
        · rw [ifp ⟨rfl, e₄⟩, ifp ⟨by omega, by omega⟩, show B * b + k - (B * b + B - L) = k - (B - L) by omega]
          rw [or0, zor]
        · rw [ifn (fun h => e₄ h.2), ifn (by omega), or0, or0]
      · have hbf : b < b + 1 := Nat.lt_succ_self b
        have : B * (b + 1) ≤ B * fb := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_succ] at this
        rw [ifn (fun h => e₃ h.1), ifn (by omega), or0, or0]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : Proof.Hmac.Stream.PPC64LE.HashOK H)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} {j : Nat} {p : Addr} (T : MdTabS H cn cc dn dc f j Sp s p)
  {P : Params} {md : Md P.B P.N P.L} (ok : CtOK P md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv D)
include L hH T ok hl

/-- `ctHash`: from `M'` of `8 + hLen + sl` bytes at `oY`, followed by zeros
up to 2048 bytes, with the salt's length `sl` in `r25`, its digest at
`oDig`; our part of the working space before the streaming state is kept. -/
theorem ctHash_ok (hD : H.D = D) (hN : H.N = P.N) (hB : H.B = P.B) {t : State} (h : Base Sp (vP D) s t)
    (sy : t.syms = s.syms) {sl : Nat} (h25 : t.gpr .r25 = BitVec.ofNat 64 sl) (hsl : sl < dN) {msg : List Byte}
    (hml : msg.length = 8 + D + sl) (hY : ∀ i < 2048, view t.mem (Sp s) (oY + i) = msg.getD i 0) :
    WP isa (ctHash H P f j) t fun t' => (Base Sp (vP D) s t' ∧ t'.gpr .r24 = t.gpr .r24 ∧
      (∀ o < oSt, view t'.mem (Sp s) o = view t.mem (Sp s) o) ∧
      ∀ i < D, view t'.mem (Sp s) (oDig + i) = (hH.SH.H.hash msg).getD i 0) ∧ t'.syms = s.syms := by
  have F := L.F
  have hR : oRsa = 8192 := rfl
  have hY' : oY = 2560 := rfl
  have hSt : oSt = 1024 := rfl
  have hSl : oSel = 4800 := rfl
  have hLn : oLen = 4608 := rfl
  have hDg : oDig = 1280 := rfl
  have hW' : oW = 1352 := rfl
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  have hNd := ok.dims.N
  have hBd := ok.dims.B
  have hLd := ok.dims.L
  have hk := L.hk; have hk2 := L.k2; have hD64 := L.D64; have hD0 := L.D0
  have hDN : D ≤ P.N := hl.DN
  have hLB : P.L < P.B := by rcases hBd with e | e <;> omega
  have hB0 : 0 < P.B := by omega
  have hS : H.S = P.N + P.B := by simp only [Hash.S, hN, hB]
  -- The lengths.
  let ℓ := 8 + D + sl
  let nbm := (dN + (8 + D - 1 + P.L)) / P.B + 1
  let fb := lastBlk P.B P.L ℓ
  have hnb : nbm * P.B ≤ 2048 := by
    have := Nat.div_mul_le_self (dN + (8 + D - 1 + P.L)) P.B
    rw [Nat.add_mul, Nat.one_mul]; rcases hBd with e | e <;> rw [e] at this ⊢ <;> omega
  have hn0 : 0 < nbm * P.B := Nat.mul_pos (Nat.succ_pos _) hB0
  have hfb : fb < nbm := by
    show (ℓ + P.L) / P.B < _ + 1
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  have hn32 : nbm ≤ 32 := by rcases hBd with e | e <;> rw [e] at hnb <;> omega
  have hcm : nbm * P.B = P.B * nbm := Nat.mul_comm _ _
  have hfbB : P.B * (fb + 1) ≤ 2048 := Nat.le_trans (Nat.mul_le_mul_left _ hfb) (by rw [← hcm]; exact hnb)
  refine WP.seq (WP.of_syms (wp_addi (h := by omega) fun t₁ o₁ e₁ => wp_addi (h := by omega) fun t₂ o₂ e₂ =>
    wp_lsr (h := by omega) fun t₃ o₃ e₃ => wp_addi (h := by decide) fun t₄ o₄ e₄ => wp_nil fun y₄ => ?_))
  have k₄ : Only [.r29, .r28] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have g29 : t₄.gpr .r29 = BitVec.ofNat 64 ℓ := by
    rw [o₄.get .r29, o₃.get .r29, o₂.get .r29, e₁, h25, hD, BitVec.ofNat_add_ofNat]; congr 1; omega
  have g28 : t₄.gpr .r28 = BitVec.ofNat 64 nbm := by
    rw [e₄, e₃, e₂, o₁.get .r21, h.pdb, L.hdb, hD, BitVec.ofNat_add_ofNat, Proof.MdStream.PPC64LE.ofNat_shr (by omega),
      hlg, BitVec.ofNat_add_ofNat]
  have b₄ := h.only F k₄
  -- `init`.
  refine WP.seq (WP.mono (hInit_ok F hH T b₄ (y₄.trans sy)) fun t₅ ⟨⟨b₅, g₅, s₅, r₅⟩, y₅⟩ => ?_)
  have iv₅ : md.stateAt t₅.mem (off (Sp s) oSt) = iv := by
    have := (hl.repr _ _ _ r₅).1
    rw [this, List.length_nil, Nat.zero_div, Md.compressList_zero]
  -- `0x80`.
  refine WP.seq (WP.of_syms (WP.mono (pad80_ok L hlg hlg7 b₅ (ℓ := ℓ) (by rw [g₅ _ (by decide), g28])
    (by rw [g₅ _ (by decide), g29]) hnb hn0 (by omega)) fun t₆ ⟨b₆, k₆, v₆⟩ y₆ => ?_))
  -- The length field.
  refine WP.seq (WP.of_syms (WP.mono (lenField_ok L ok.shape ok.lenLr (by rcases hBd with e | e <;> omega) hLd.2 hlg7 (ℓ := ℓ)
    b₆ (by rw [k₆.get .r29, g₅ _ (by decide), g29]) (by omega)) fun t₇ ⟨b₇, k₇, g27, m₇⟩ y₇ => ?_))
  rw [md.lenOf_eq _ (ok.lenOk _ (by omega))] at m₇
  have g27' : t₇.gpr .r27 = BitVec.ofNat 64 fb := by rw [g27, hlg]; rfl
  -- Into the last block.
  have v₇ : ∀ o < oRsa, view t₇.mem (Sp s) o =
      if oLen ≤ o ∧ o < oLen + P.L then (md.lenBytes ℓ).getD (o - oLen) 0 else view t₆.mem (Sp s) o := by
    intro o ho; rw [m₇, view_wb _ _ (by rw [md.lenBytes_length]; omega) ho, md.lenBytes_length]
  refine WP.seq (WP.of_syms (WP.mono (lenLoop_ok L hBd hLB hLd.1 b₇
    (by rw [k₇.get .r28, k₆.get .r28, g₅ _ (by decide), g28]) g27' (by omega) hnb (by omega)
    (len := md.lenBytes ℓ) (fun i hi => by rw [v₇ _ (by omega), ifp ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]))
    fun t₈ ⟨b₈, k₈, v₈⟩ y₈ => ?_))
  -- The compression.
  have hst₈ : md.stateAt t₈.mem (off (Sp s) oSt) = iv := by
    rw [← iv₅]
    refine md.stateAt_congr fun i hi => ?_
    have e8 := v₈ (oSt + i) (by omega)
    rw [vLen_lt _ _ _ _ _ _ _ (by omega), v₇ _ (by omega), ifn (by omega), v₆ _ (by omega)] at e8
    simp only [v80] at e8
    rw [ifn (by omega)] at e8
    rw [off_add']; exact e8
  refine WP.seq (WP.mono (compLoop_ok L T ok b₈ (y₈.trans (y₇.trans (y₆.trans y₅)))
    (by rw [k₈.get .r28, k₇.get .r28, k₆.get .r28, g₅ _ (by decide), g28])
    (by rw [k₈.get .r27, g27']) (Nat.succ_pos _) hnb hfb) fun t₉ I => ?_)
  rw [hst₈] at I
  -- The digest.
  refine WP.seq (WP.of_syms (wp_addi (h := by decide) fun t₁₀ o₁₀ e₁₀ => wp_addi (h := by decide)
    fun t₁₁ o₁₁ e₁₁ => wp_nil fun y₁₁ => ?_))
  have k₁₁ : Only [.r3, .r4] t₉ t₁₁ := (o₁₀.trans o₁₁).mono
  refine WP.mono (digM_ok F T ok.dig ok.digNF hNd.2 (I.base.only F k₁₁) (y₁₁.trans I.sy)
    (by rw [o₁₁.get .r3, e₁₀, I.base.r14]) (by rw [e₁₁, o₁₀.get .r14, I.base.r14])) fun t' ⟨⟨b', g', s', m'⟩, y'⟩ =>
    ⟨⟨b', ?_, fun o ho => ?_, fun i hi => ?_⟩, y'⟩
  · rw [g' _ (by decide), k₁₁.get .r24, I.keep .r24 (by simp), k₈.get .r24, k₇.get .r24, k₆.get .r24,
      g₅ _ (by decide), k₄.get .r24]
  · rw [s' o (by omega) (by simp; omega), show view t₁₁.mem (Sp s) o = view t₉.mem (Sp s) o by rw [k₁₁.mem],
      I.mem o (by omega) (.inl ho), v₈ o (by omega), vLen_lt _ _ _ _ _ _ _ (by omega), v₇ o (by omega),
      ifn (by omega), v₆ o (by omega)]
    simp only [v80]
    rw [ifn (by omega), s₅ o (by omega) (by simp; omega), show view t₄.mem (Sp s) o = view t.mem (Sp s) o by
      rw [k₄.mem]]
  · -- The selected hash value is that of the padded message.
    have hsel := I.sel hfb
    have hpad : md.compressList iv (yl (view t₈.mem (Sp s))) (fb + 1) =
        md.compressList iv (md.pad msg) ((md.pad msg).length / P.B) := by
      rw [RsaPss.pad_length md msg hB0 hLB, Nat.mul_div_cancel_left _ hB0, hml]
      refine md.compressList_congr fun j hj => ?_
      rw [RsaPss.pad_getD md msg hB0 hLB (by rw [hml]; exact hj), yl_getD (by omega), v₈ _ (by omega)]
      refine (y_pad msg _ (by rw [hml]) hLB hfb _ (fun j' hj' => ?_) j hj).trans (by rw [hml])
      rw [v₇ _ (by omega), ifn (by omega), v₆ _ (by omega)]
      simp only [v80]
      rw [ifp ⟨by omega, by omega⟩, Nat.add_sub_cancel_left, s₅ _ (by omega) (by simp; omega),
        show view t₄.mem (Sp s) (oY + j') = view t.mem (Sp s) (oY + j') by rw [k₄.mem], hY j' (by omega), hml]
    have hdl := md.digest_length (md.stateAt t₁₁.mem (off (Sp s) oSel))
    rw [m', view_wb _ _ (by rw [hdl]; omega) (by omega), ifp ⟨by omega, by rw [hdl]; omega⟩, Nat.add_sub_cancel_left,
      k₁₁.mem, hsel, hpad, hl.hash]
    show (md.hash iv msg).getD i 0 = ((md.hash iv msg).take D).getD i 0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

end

end VG.Proof.RsaPss.PPC64LE
