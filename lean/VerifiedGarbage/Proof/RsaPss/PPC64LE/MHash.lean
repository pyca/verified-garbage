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
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW sc_cov sdis cR_dis Same)
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

end VG.Proof.RsaPss.PPC64LE
