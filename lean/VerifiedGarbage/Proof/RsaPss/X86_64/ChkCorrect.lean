module

public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBlocks
public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyPadding
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBack
import VerifiedGarbage.Proof.RsaPss.X86_64.PrefixCheck
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.RsaPss.X86_64.EncParams
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect

/-!
# EMSA-PSS's check of an encoding on x86-64: correctness

`chk_ok`: from the entry state, `checkEncoding` copies the encoding to its
working space, checks the lengths, and returns 1 exactly when
`Spec.RsaPss.verifyEncoding` holds (`cpadding_done`, verification's checks
from `VerifyPadding`), with the callee-saved registers restored;
`chk_correct`: it meets `chkK`, keeping its return address and MXCSR's
control bits.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable {G : Spec.Mgf1.Hash}

variable (G) in
/-- What `chkK.post` asks of `rax`. -/
def chkOut (s : State) : Bool :=
  Spec.RsaPss.verifyEncoding G G (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) G.len)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (s.gpr .rcx).toNat
    (Spec.RsaPss.expectedSaltLen (s.gpr .r8) ((s.gpr .r9).setWidth 32))

/-- Before the epilogue: the result in `rax`, the saved registers in their
slots. -/
structure CDone (result : Bool) (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 0)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : (t.gpr .rax).setWidth 32 = if result then 1 else 0

/-- A refusal: 0. -/
theorem ret0_done {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 0)) (R : Rep t.mem (fb s) (stackArg s 0) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12) :
    WP isa ret0 t (CDone false s) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rax = 0) ?_ rfl)
    fun t' ⟨⟨hm, hax⟩, k⟩ => ?_
  · xrun [ret0]
  have R' : Rep t'.mem (fb s) (stackArg s 0) V W := hm ▸ R
  refine ⟨L.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), k.2.2.trans hw,
    fun r hr => (k.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)).trans (hcs r hr), ?_, ?_, ?_, ?_⟩
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · rw [hax]; rfl

/-- `sAny := any_salt_len ≠ 0`, and `rdx` the salt length the encoding must
fit, 0 for any. -/
theorem anyReg_ok {s u : State} {S : Addr} (L : Lay u (fb s) S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem (fb s) S V W) (h36 : W 36 = s.gpr .r8) (h9 : u.gpr .r9 = s.gpr .r9) :
    WP isa anyReg u fun u' => Lay u' (fb s) S ∧ Keep [.rax, .rdx] u u' ∧
      Rep u'.mem (fb s) S V (upd W 35 (if (s.gpr .r9).setWidth 32 = 0 then 0 else 1)) ∧
      u'.gpr .rdx = if (s.gpr .r9).setWidth 32 = 0 then s.gpr .r8 else 0 := by
  have G' := L.geo
  have R2 := R.wf G' (k := 35) (by decide) (if (s.gpr .r9).setWidth 32 = 0 then 0 else 1)
  rw [show off (fb s) (8 * 35) = off (fb s) sAny from rfl] at R2
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun v => v.mem = u.mem ∧
      v.zf = some (decide ((s.gpr .r9).setWidth 32 = 0))) ?_ rfl) fun v ⟨⟨hm, hz⟩, hk⟩ => ?_)
  · xrun [anyReg, h9]
    rw [BitVec.and_self, zext32_beq_zero]
  have Lv : Lay v (fb s) S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem (fb s) S V W := hm ▸ R
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hz) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    rw [ifp hb] at R2 ⊢
    rw [ifp hb]
    have R2' : Rep (v.mem.writeW (off (fb s) sAny) (0 : BitVec 64)) (fb s) S V (upd W 35 0) := by
      rw [hm]; exact R2
    have e36 : (v.mem.writeW (off (fb s) sAny) (0 : BitVec 64)).readW (off (fb s) sSlen) 64 = s.gpr .r8 := by
      rw [R2'.rd (d := sSlen) 36 rfl (by decide)]; simp [upd, h36]
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun w => w.mem = v.mem.writeW (off (fb s) sAny) (0 : BitVec 64) ∧
        w.gpr .rdx = s.gpr .r8) ?_ rfl)
      fun w ⟨⟨hm', hdx⟩, k'⟩ => ⟨Lv.of_rep' Rv (hm' ▸ R2') (by simp [upd]) (k'.gpr (by decide)) k'.2.2,
        (hk.trans k').mono (by decide), hm' ▸ R2', hdx⟩
    xrun [ea_sp, Lv.rsp, Lv.st (d := sAny) (by decide), Lv.ld (d := sSlen) (by decide),
      show BitVec.setWidth 64 (0 : BitVec 32) = (0 : BitVec 64) from rfl, e36]
  · rw [decide_eq_false_iff_not] at hb
    rw [ifn hb] at R2 ⊢
    rw [ifn hb]
    have R2' : Rep (v.mem.writeW (off (fb s) sAny) (1 : BitVec 64)) (fb s) S V (upd W 35 1) := by
      rw [hm]; exact R2
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun w => w.mem = v.mem.writeW (off (fb s) sAny) (1 : BitVec 64) ∧
        w.gpr .rdx = 0) ?_ rfl)
      fun w ⟨⟨hm', hdx⟩, k'⟩ => ⟨Lv.of_rep' Rv (hm' ▸ R2') (by simp [upd]) (k'.gpr (by decide)) k'.2.2,
        (hk.trans k').mono (by decide), hm' ▸ R2', hdx⟩
    xrun [ea_sp, Lv.rsp, Lv.st (d := sAny) (by decide)]
    rfl

/-- The encoding's `emLen` bytes copied to `scratch + oEm`. -/
theorem copyIn_ok {s u : State} (hp : Pre G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 0)) (R : Rep u.mem (fb s) (stackArg s 0) V W) (hw : u.wr = frR s :: s.wr)
    (hrd : u.rd = s.rd) (h17 : W 17 = s.gpr .rdx) (h38 : W 38 = s.gpr .rsi) :
    WP isa copyIn u fun u' => Lay u' (fb s) (stackArg s 0) ∧ Keep [.rcx, .rsi, .r10, .rax, .r8] u u' ∧
      Rep u'.mem (fb s) (stackArg s 0)
        (cpV V (fun i => u.mem (s.gpr .rsi + BitVec.ofNat 64 i)) (oEm + 0) (s.gpr .rdx).toNat) W := by
  have hk2 := hp.k2
  have hk1 : 1 ≤ (s.gpr .rdx).toNat := by
    have := hp.hel; have := hp.b1; unfold Spec.RsaPss.emLength at *; omega
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rcx, .rsi, .r10, .r8] (Q := fun v => v.gpr .rcx = off (stackArg s 0) oEm ∧
      v.gpr .rsi = s.gpr .rsi ∧ v.gpr .r10 = BitVec.ofNat 64 (s.gpr .rdx).toNat ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧
      v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₁₀, h₃, hm⟩, hkv⟩ => ?_)
  · xrun [copyIn, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide),
      L.ld (d := sSig) (by decide), L.ld (d := sK) (by decide), hs, R.rd (d := sSig) 38 rfl (by decide),
      R.rd (d := sK) 17 rfl (by decide), h17, h38, VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide)]
    simp
  have Lv : Lay v (fb s) (stackArg s 0) := L.congr (hkv.gpr (by decide)) hkv.2.2 (by rw [hm])
  refine WP.mono (copy_ok Lv (hm ▸ R) (d := .rcx) (by decide) (p := s.gpr .rsi) (o := oEm) (disp := 0)
    (n := (s.gpr .rdx).toNat) (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₁₀)
    (by omega) (by unfold oEm oRsa; omega) h₂ h₁ h₃
    (fun i hi => ⟨⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, List.mem_append_left _ (by rw [hkv.2.1, hrd, hp.hrd]; simp),
      Offset.contains_base _ (by have := hp.wEm; omega) (by omega)⟩)
    (fun i hi j hj => Outside.ne Lv (by
      have := hp.outside hp.dems hp.dKem (a := s.gpr .rsi + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by have := hp.wEm; omega) (by omega))
      rwa [hkv.2.2, hw]) (by unfold oEm oRsa; omega)))
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hkv.trans kw).mono (by decide), by rw [hm] at Rw; exact Rw⟩

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
/-- Padding verification depends only on the recovered bytes, not on how
RSA produced them. -/
theorem cpadding_done (lk : Pbkdf2.Md.X86_64.MgfLink H hH)
    {s u3 : State} (hp : Pre lk.G s) {V1 : Nat → Byte} {W1 : Nat → BitVec 64}
    (L3 : Lay u3 (fb s) (stackArg s 0)) (R1 : Rep u3.mem (fb s) (stackArg s 0) V1 W1)
    (hw : u3.wr = frR s :: s.wr) (hrd : u3.rd = s.rd)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], u3.gpr r = s.gpr r) (hM3 : Frame (wrR s) s.mem u3.mem)
    {lo z : Nat} {fixed result : Bool} (x : List Byte) (hxl : x.length = (s.gpr .rdx).toNat)
    (hV1 : ∀ i < (s.gpr .rdx).toNat, V1 (oEm + i) = x.getD i 0)
    (h17 : W1 17 = s.gpr .rdx) (h23 : W1 23 = off (stackArg s 0) (oEm + lo))
    (h24 : W1 24 = BitVec.ofNat 64 ((s.gpr .rdx).toNat - lo - lk.G.len - 1))
    (h25 : W1 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z)) (h26 : W1 26 = BitVec.ofNat 64 lo)
    (h35 : W1 35 = if fixed then 0 else 1) (h36 : W1 36 = s.gpr .r8) (h37 : W1 37 = s.gpr .rdi)
    (h41 : W1 41 = s.gpr .rbx) (h42 : W1 42 = s.gpr .rbp) (h43 : W1 43 = s.gpr .r12)
    (hlo : lo ≤ 1) (hfit : H.D + 2 ≤ (s.gpr .rdx).toNat - lo)
    (hspec : result = true ↔ (lo = 1 → x.getD 0 0 = 0) ∧
      EncOk lk.G (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) lk.G.len) (x.drop lo) ((s.gpr .rdx).toNat - lo) z
        (Spec.RsaPss.expectedSaltLen (s.gpr .r8) ((s.gpr .r9).setWidth 32)))
    (hsl : Spec.RsaPss.expectedSaltLen (s.gpr .r8) ((s.gpr .r9).setWidth 32) =
      if fixed then some (s.gpr .r8).toNat else none) :
    WP isa (seqs [.block acc0, mgfXor H, .block clearTop, scanCheck H,
      saltBack H]) u3 (CDone result s) := by
  have hk2 := hp.k2
  have hD : H.D = lk.G.len := lk.len.symm
  have hG := validG hH lk.hash lk.len
  have c1 : oEm = 2560 := rfl
  have c5 : oRsa = 8192 := rfl
  rw [show [Code.block acc0, mgfXor H, .block clearTop, scanCheck H,
      saltBack H] =
    [Code.block acc0, mgfXor H, .block clearTop, scanCheck H] ++
    [saltBack H] from rfl]
  set k := (s.gpr .rdx).toNat with hk
  set db := k - lo - lk.G.len - 1 with hdb
  -- `acc` and the first nonzero byte of `DB`.
  refine WP.seqs_append (by simp) (by simp) (WP.mono (WP.keepIn (vmid_safe hH K) (by rw [vmid_xd K])
    (vmid_ok hH K lk L3 R1 (k := k) (lo := lo) (db := db) (z := z) (fixed := fixed)
      (by rw [h17, hk, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      h23 h24 (by rw [h25])
      (by rw [h26])
      (by rw [h35]) hlo (by omega_arith) (by omega_arith) hk2))
    fun u4 ⟨⟨L4, rd4, wr4, cs4, V3, W3, R3, h33, h34, h27, hW3, hV3, hO3⟩, f4⟩ => ?_)
  have hM4 := frame_keep hp hw L3.rsp hM3 f4
  -- `DB` as the specification's.
  have hm1 : (List.range db).map (fun i => V1 (oEm + lo + i)) = (x.drop lo).take db :=
    map_range_drop (by omega_arith) fun i hi => by rw [Nat.add_assoc, hV1 _ (by omega_arith)]
  have hm2 : (List.range H.D).map (fun i => V1 (oEm + lo + db + i)) = vH lk.G (x.drop lo) db := by
    have hl : db + H.D ≤ (x.drop lo).length := by rw [List.length_drop, hxl]; omega_arith
    have h := map_range_drop (x := x.drop lo) (lo := db) (n := H.D) (f := fun i => V1 (oEm + lo + db + i)) hl
      (fun i hi => by
        rw [show oEm + lo + db + i = oEm + (lo + (db + i)) by omega_arith, hV1 _ (by omega_arith)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop])
    rw [h, vH, hD]
  rw [hm1, hm2] at h33 hV3
  rw [hm1, hm2] at h34 h27
  have hvdb : Spec.RsaPss.clearTop z (Spec.Mgf1.xorBytes ((x.drop lo).take db)
      (Spec.Mgf1.mgf1 lk.G (vH lk.G (x.drop lo) db) db)) = vDb lk.G (x.drop lo) db z := rfl
  rw [hvdb] at h33 hV3 h34 h27
  set dbL := vDb lk.G (x.drop lo) db z with hdbL
  have h23' : W3 23 = off (stackArg s 0) (oEm + lo) := by rw [hW3 23 (by decide) (.inl (by decide)), h23]
  have h24' : W3 24 = BitVec.ofNat 64 db := by rw [hW3 24 (by decide) (.inl (by decide)), h24]
  have h37' : W3 37 = s.gpr .rdi := by
    rw [hW3 37 (by decide) (.inr (by decide)), h37]
  set posF := if (fixed && decide ((W1 36).toNat < db)) = true then db - (W1 36).toNat - 1
    else if lz dbL < db then lz dbL else 0 with hposF
  have hpd : posF < db := by rw [hposF]; split <;> [omega_arith; split <;> omega_arith]
  have hrd4 : u4.rd = s.rd := by rw [rd4, hrd]
  have hwr4 : u4.wr = frR s :: s.wr := by rw [wr4, hw]
  have wDg := hp.wDg
  -- The salt, its hash, and the comparison.
  refine WP.mono (WP.keepIn (saltBack_safe hH K) (by rw [saltBack_xd K])
    (saltBack_ok hH K lk L4 R3 (lo := lo) (db := db) (pos := posF) (dig := s.gpr .rdi)
      h23' h24' h34 h27 h37' hlo (by omega_arith) hpd (by omega_arith)
      (fun i hi => by
        rw [hrd4]
        exact ⟨⟨s.gpr .rdi, lk.G.len⟩, List.mem_append_left _ (by rw [hp.hrd]; simp),
          Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      (fun i hi => by
        have := hp.outside hp.ddgs hp.dKdg (a := s.gpr .rdi + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega_arith) (by omega_arith))
        rwa [← hwr4] at this)
      (fun hany hacc => by
        have hfixed : fixed = true := by
          rw [hW3 35 (by decide) (.inr (by decide)), h35] at hany
          cases fixed <;> first | rfl | simp at hany
        rw [h33] at hacc
        rw [hW3 36 (by decide) (.inr (by decide))]
        by_cases hff : (fixed && decide ((W1 36).toNat < db)) = true
        · have hlt : (W1 36).toNat < db := by simpa [hfixed] using hff
          have hpF : posF = db - (W1 36).toNat - 1 := by rw [hposF, ifp hff]
          rw [hpF, show db - (db - (W1 36).toNat - 1) - 1 = (W1 36).toNat by omega_arith]
          simp
        · rw [ifn hff] at hacc
          exact (hacc.2.2.2 hfixed).symm)))
    fun u5 ⟨⟨L5, rd5, wr5, cs5, ⟨V5, W5, R5, hW5⟩, hax5⟩, f5⟩ => ?_
  have g3 : ∀ j, j < nW → 34 < j → W3 j = W1 j := fun j hj h => hW3 j hj (.inr h)
  have g5 : ∀ j, j < nW → 34 < j → j ≠ 44 → j ≠ 45 → j ≠ 46 → W5 j = W1 j := fun j hj h a b c =>
    (hW5 j hj (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) a b c).trans (g3 j hj h)
  refine ⟨L5, by rw [wr5, hwr4], fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have hr' : r ∈ [Reg.r13, .r14, .r15, .rsp] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [cs5 r hr', cs4 r hr', hcs r hr]
  · rw [R5.rd (d := sRbx) 41 rfl (by decide), g5 41 (by decide) (by decide) (by decide) (by decide) (by decide), h41]
  · rw [R5.rd (d := sRbp) 42 rfl (by decide), g5 42 (by decide) (by decide) (by decide) (by decide) (by decide), h42]
  · rw [R5.rd (d := sR12) 43 rfl (by decide), g5 43 (by decide) (by decide) (by decide) (by decide) (by decide), h43]
  -- The result.
  have hmsg1 : (List.range H.D).map (bytesF u4.mem (s.gpr .rdi)) = Spec.Rsa.bytesAt s.mem (s.gpr .rdi) lk.G.len := by
    rw [hD]; exact bytesAt_frame hM4 (in_apart hp.dKdg hp.ddgs) (by omega_arith)
  have hdbl : dbL.length = db := by
    rw [hdbL, vDb, clearTop_length, Proof.Mgf1.xorBytes_length, Proof.Mgf1.mgf1_length hG]; simp; omega_arith
  have hmsg2 : (List.range db).map (fun i => V3 (oEm + lo + i)) = dbL :=
    (eq_range_map hdbl (fun i hi => (hV3 i hi).symm)).symm
  have hHb : ∀ i < H.D, V3 (oEm + lo + db + i) = (vH lk.G (x.drop lo) db).getD i 0 := fun i hi => by
    rw [hO3 _ (by omega_arith) ⟨by unfold oLen; omega_arith, by unfold oY; omega_arith⟩ (by omega_arith),
      show oEm + lo + db + i = oEm + (lo + (db + i)) by omega_arith, hV1 _ (by omega_arith)]
    simp only [vH, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, ifp (show i < lk.G.len by omega_arith)]
  have hV := vlogic lk.G hG x (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) lk.G.len) (z := z) fixed (s.gpr .r8) hsl hxl hlo
    (by omega_arith) hk2
  simp only [← hdb, ← hdbL] at hV
  rw [hax5, hmsg1, hmsg2]
  refine ite_setWidth ((Iff.trans ?_ hV).trans hspec.symm)
  have e0 : acc0V (V1 (oEm + k - 1)) (V1 oEm) (V1 (oEm + lo)) ((0xFF : Byte) >>> z) lo =
      acc0V (x.getD (k - 1) 0) (x.getD 0 0) (x.getD lo 0) ((0xFF : Byte) >>> z) lo := by
    have h0 := hV1 0 (by omega_arith)
    rw [Nat.add_zero] at h0
    rw [hV1 lo (by omega_arith), show oEm + k - 1 = oEm + (k - 1) by omega_arith, hV1 _ (by omega_arith), h0]
  have hHC : ∀ q, (∀ i < H.D, (lk.G.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (s.gpr .rdi) lk.G.len ++
      dbL.drop (q + 1))).getD i 0 = V3 (oEm + lo + db + i)) ↔
      (∀ i < lk.G.len, (lk.G.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (s.gpr .rdi) lk.G.len ++
      dbL.drop (q + 1))).getD i 0 = (vH lk.G (x.drop lo) db).getD i 0) := fun q => by
    rw [← hD]
    exact forall_congr' fun i => imp_congr_right fun hi => by rw [hHb i hi]
  rw [h33, e0, acc1V_eq_zero, ← h36]
  by_cases hff : (fixed && decide ((W1 36).toNat < db)) = true
  · have hfx : fixed = true := (Bool.and_eq_true_iff.mp hff).1
    have hlt : (W1 36).toNat < db := by simpa [hfx] using hff
    have hpF : posF = db - (W1 36).toNat - 1 := by rw [hposF, ifp hff]
    rw [ifp hff, hpF, fixed_cond dbL hdbl hlt]
    have hsl64 : BitVec.ofNat 64 (W1 36).toNat = W1 36 := by simp
    constructor
    · rintro ⟨⟨ha, hl, h1, hsl'⟩, hh⟩
      have hlz : lz dbL = db - (W1 36).toNat - 1 := by omega_arith
      refine ⟨⟨ha, by rw [ifp hl]; exact h1, decide_eq_true hl, fun _ => ?_⟩, ?_⟩
      · rw [ifp hl, hsl', hsl64]
      · rw [ifp hl, hlz]; exact (hHC _).mp hh
    · rintro ⟨⟨ha, h1, hfd, hsl'⟩, hh⟩
      have hl : lz dbL < db := of_decide_eq_true hfd
      rw [ifp hl] at h1 hsl' hh
      have hsl'' : db - lz dbL - 1 = (W1 36).toNat := by
        have := congrArg BitVec.toNat (hsl' hfx)
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      have hlz : lz dbL = db - (W1 36).toNat - 1 := by omega_arith
      exact ⟨⟨ha, hl, h1, hsl''⟩, by rw [← hlz]; exact (hHC _).mpr hh⟩
  · have hpF : posF = if lz dbL < db then lz dbL else 0 := by rw [hposF, ifn hff]
    rw [ifn hff, hpF]
    exact and_congr Iff.rfl (hHC _)


include hH K in
theorem chkBody_safe : (chkBody H).allInstrs safeI = true := by
  simp only [chkBody, chkMain, chkPrologue, maskBits, fitH, ret0, saltFits, copyIn, anyReg, seqs, Code.allInstrs,
    mgfXor_safe hH K, saltBack_safe hH K, rec_all, List.all_append, scanCheck, prefixCheck, prefixWords,
    prefixBytes, posScan, posCheck, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include K in
theorem chkBody_xd : (chkBody H).x86_64Depth = 8 := by
  simp only [chkBody, chkMain, ret0, copyIn, anyReg, seqs, Code.x86_64Depth, mgfXor_xd K, saltBack_xd K, scanCheck,
    prefixCheck, prefixWords, prefixBytes, posScan, posCheck, byteLoop]
  rfl

include hH K in
theorem chk_spAll : (checkEncoding H).allInstrs (fun i => !isa.writesSp i) = true := by
  have he := chkBody_safe hH K
  rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at he
  simp only [checkEncoding, Code.allInstrs, he.1]
  rfl

include K in
theorem chk_xd : (checkEncoding H).x86_64Depth ≤ chkStack := by
  simp only [checkEncoding, Code.x86_64Depth, chkBody_xd K, X86_64.Instr.frameBytes]
  unfold chkStack frameBytes
  decide

/-- The epilogue: the callee-saved registers restored and the outcome. -/
theorem restore_ok {s t : State} (D : CDone (chkOut G s) s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      (∀ r ∈ calleeSaved, (freedF t').gpr r = s.gpr r) ∧ (chkK G).post s (freedF t') := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rbx = s.gpr .rbx ∧
      t'.gpr .rbp = s.gpr .rbp ∧ t'.gpr .r12 = s.gpr .r12) ?_ rfl) fun t' ⟨⟨hm, h1, h2, h3⟩, k⟩ => ?_
  · xrun [restoreRegs, ea_sp, D.L.rsp, D.L.ld (d := sRbx) (by decide), D.L.ld (d := sRbp) (by decide),
      D.L.ld (d := sR12) (by decide), D.rbx, D.rbp, D.r12]
  have hsp : t'.gpr .rsp = fb s := (k.gpr (by decide)).trans D.L.rsp
  refine ⟨hsp, k.2.2.trans D.wr, fun r hr => ?_, ?_⟩
  · simp only [freedF, State.setReg]
    by_cases hr' : r = .rsp
    · subst hr'; simp only [ite_true, hsp, fb]; exact BitVec.sub_add_cancel _ _
    · simp only [hr', ite_false]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact absurd rfl hr'
      · exact h3
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
  · show ((freedF t').gpr .rax).setWidth 32 = _
    have hax : (freedF t').gpr .rax = t.gpr .rax := by
      show (if Reg.rax = Reg.rsp then t'.gpr .rsp + BitVec.ofNat 64 frameBytes else t'.gpr .rax) = _
      rw [ifn (by decide), k.gpr (by decide)]
    rw [hax]
    exact D.out

include hH K in
theorem chk_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {s : State} (h : (chkK lk.G).pre s) :
    WP isa (checkEncoding H) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ (chkK lk.G).post s s' ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hp := Pre.of lk.G h
  have hF := fb_toNat hp
  have hk2 := hp.k2
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hGl : lk.G.len = H.D := lk.len
  have hG := validG hH lk.hash lk.len
  have hel := hp.hel
  refine wp_frame (by have := hp.sp1; unfold chkStack frameBytes at *; omega) ?_
  refine WP.mono_mx (safe_mx (chkBody_safe hH K)) (Q := fun s₂ => s₂.gpr .rsp = fb s ∧
    s₂.wr = (allocState frameBytes s).wr ∧ (∀ r ∈ calleeSaved, (freedF s₂).gpr r = s.gpr r) ∧
      (chkK lk.G).post s (freedF s₂)) ?_ fun t ⟨a, b, c, d⟩ hmx =>
    ⟨a, b, c, d, by rw [show (freedF t).mxcsr = t.mxcsr from rfl, hmx]; rfl⟩
  rw [chkBody]
  simp only [seqs]
  -- The prologue.
  refine WP.seq (WP.mono (chkPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ => ?_)
  have hM1 : Frame (wrR s) s.mem t1.mem := frame_wrR f1
  -- The encoding, copied.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [copyIn]) (by exact Nat.zero_le 8)
    (copyIn_ok hp L1 R1 k1.2.2 k1.2.1 (by simp [proW', proW, upd]) (by simp [proW', proW, upd])))
    fun t2 ⟨⟨L2, k2, R2⟩, f2⟩ => ?_)
  have hM2 := frame_keep hp k1.2.2 L1.rsp hM1 f2
  have hw2 : t2.wr = frR s :: s.wr := k2.2.2.trans k1.2.2
  -- The salt length's arguments.
  have h9 : t2.gpr .r9 = s.gpr .r9 := by
    rw [k2.gpr (by decide), k1.gpr (by decide)]; simp only [allocState_gpr']; rfl
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [anyReg]) (by exact Nat.zero_le 8)
    (anyReg_ok L2 R2 (by simp [proW', proW, upd]) h9)) fun t3 ⟨⟨L3, k3, R3, hdx3⟩, f3⟩ => ?_)
  have hM3 := frame_keep hp hw2 L2.rsp hM2 f3
  have hw3 : t3.wr = frR s :: s.wr := k3.2.2.trans hw2
  -- `emLen ≥ hLen + 2`.
  refine WP.seq (WP.mono (fitH_ok (H := H) (by omega) L3 R3 (k := (s.gpr .rdx).toNat)
    (by simp only [upd, proW', proW, Nat.reduceEqDiff, ite_true, ite_false]; rw [BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (by omega)) fun t4 ⟨k4, hm4, hax4, hc4⟩ => ?_)
  have L4 : Lay t4 (fb s) (stackArg s 0) := L3.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
  have R4 := hm4 ▸ R3
  have hM4 : Frame (wrR s) s.mem t4.mem := hm4 ▸ hM3
  have hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans hw3
  have hrd4 : t4.rd = s.rd := k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))
  have hcs4 : ∀ r ∈ [Reg.r13, .r14, .r15], t4.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rax] ∧ r ∉ [Reg.rax, .rdx] ∧ r ∉ [Reg.rcx, .rsi, .r10, .rax, .r8] ∧ r ∉ [Reg.rax, .rcx] := by
      simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k4.gpr this.1, k3.gpr this.2.1, k2.gpr this.2.2.1, k1.gpr this.2.2.2]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  refine WP.seq (WP.mono (Q := CDone (chkOut lk.G s) s) ?_ fun t D => restore_ok D)
  set fixed := decide ((s.gpr .r9).setWidth 32 = 0) with hfixed
  set sLen := Spec.RsaPss.expectedSaltLen (s.gpr .r8) ((s.gpr .r9).setWidth 32) with hsLen
  have hsl : sLen = if fixed then some (s.gpr .r8).toNat else none := expectedSaltLen_eq _ _
  have hlenD : (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) lk.G.len).length = lk.G.len := by simp [Spec.Rsa.bytesAt]
  have hlenE : (Spec.Rsa.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat).length = (s.gpr .rdx).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hshort : (s.gpr .rdx).toNat < lk.G.len + sLen.getD 0 + 2 → chkOut lk.G s = false := fun h => by
    unfold chkOut Spec.RsaPss.verifyEncoding
    rw [ifp (Or.inr (Or.inr (by rw [← hel]; exact h)))]
  have hfail : ∀ {t : State} {V : Nat → Byte} {W : Nat → BitVec 64}, Lay t (fb s) (stackArg s 0) →
      Rep t.mem (fb s) (stackArg s 0) V W → t.wr = frR s :: s.wr →
      (∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r) →
      W 41 = s.gpr .rbx → W 42 = s.gpr .rbp → W 43 = s.gpr .r12 → chkOut lk.G s = false →
      WP isa ret0 t (CDone (chkOut lk.G s) s) := fun L R hw hcs a b c hf => by
    rw [hf]; exact ret0_done L R hw hcs a b c
  refine WP.ite (M := isa) _ (show isa.eval .b t4 = _ from hc4) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    exact hfail L4 R4 hw4 hcs4 (by simp [upd, proW', proW]) (by simp [upd, proW', proW])
      (by simp [upd, proW', proW]) (hshort (by rw [hGl]; omega))
  rw [decide_eq_false_iff_not] at hb
  have hdx3' : t4.gpr .rdx = BitVec.ofNat 64 (sLen.getD 0) := by
    rw [k4.gpr (by decide), hdx3, hsl, hfixed]
    by_cases hf : (s.gpr .r9).setWidth 32 = 0
    · rw [ifp hf, decide_eq_true hf, ifp rfl, Option.getD_some, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [ifn hf, decide_eq_false hf]; rfl
  -- The salt fits.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (s.gpr .rdx).toNat ∧
      t.mem = t4.mem) (by
    xrun [ea_sp, L4.rsp, L4.ld (d := sK) (by decide), L4.ld (d := sLo) (by decide), R4.rd (d := sK) 17 rfl (by decide),
      R4.rd (d := sLo) 26 rfl (by decide)]
    simp only [upd, proW', proW, Nat.reduceEqDiff, ite_true, ite_false]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.sub_zero _) rfl) fun t6 ⟨⟨hax6, hm6⟩, k6⟩ => ?_
  refine WP.mono (saltFits_ok (H := H) (by omega) t6 (a := (s.gpr .rdx).toNat)
    (b := BitVec.ofNat 64 (sLen.getD 0)) (by omega) (by omega) hax6 (by rw [k6.gpr (by decide)]; exact hdx3'))
    fun t7 ⟨k7, hm7, hax7, hc7⟩ => ?_
  have hsl0 : (BitVec.ofNat 64 (sLen.getD 0)).toNat = sLen.getD 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rw [hsl]; split
    · exact (s.gpr .r8).isLt
    · simp
  rw [hsl0] at hc7
  have L7 : Lay t7 (fb s) (stackArg s 0) := L4.congr ((k7.gpr (by decide)).trans (k6.gpr (by decide)))
    (k7.2.2.trans k6.2.2) (by rw [hm7, hm6])
  have hm74 : t7.mem = t4.mem := by rw [hm7, hm6]
  have R7 := hm74 ▸ R4
  have hw7 : t7.wr = frR s :: s.wr := k7.2.2.trans (k6.2.2.trans hw4)
  have hrd7 : t7.rd = s.rd := k7.2.1.trans (k6.2.1.trans hrd4)
  have hcs7 : ∀ r ∈ [Reg.r13, .r14, .r15], t7.gpr r = s.gpr r := fun r hr => by
    rw [k7.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k6.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs4 r hr]
  have hM7 : Frame (wrR s) s.mem t7.mem := hm74 ▸ hM4
  refine WP.ite (M := isa) _ (show isa.eval .b t7 = _ from hc7) (fun hb7 => ?_) (fun hb7 => ?_)
  · rw [decide_eq_true_eq] at hb7
    exact hfail L7 R7 hw7 hcs7 (by simp [upd, proW', proW]) (by simp [upd, proW', proW])
      (by simp [upd, proW', proW]) (hshort (by rw [hGl]; omega))
  rw [decide_eq_false_iff_not] at hb7
  -- `DB`'s slots, and the checks.
  rw [chkMain]
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 8)
    (dbSlots_ok L7 R7 (lo := 0) (by simp [upd, proW']) hax7)) fun u1 ⟨⟨L8, k8, R8⟩, f8⟩ => ?_)
  have hM8 := frame_keep hp hw7 L7.rsp hM7 f8
  -- The encoding's bytes.
  have hem : ∀ i < (s.gpr .rdx).toNat, t1.mem (s.gpr .rsi + BitVec.ofNat 64 i) =
      (Spec.Rsa.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat).getD i 0 := fun i hi => by
    have := bytesAt_frame hM1 (in_apart hp.dKem hp.dems) (by omega) (p := s.gpr .rsi) (len := (s.gpr .rdx).toNat)
    rw [← this]
    simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]
  have hz : 8 * (s.gpr .rdx).toNat - (s.gpr .rcx).toNat < 8 := by
    rw [hel]; exact (emLength_z).1
  refine cpadding_done hH K lk hp L8 R8 (k8.2.2.trans hw7) (k8.2.1.trans hrd7)
    (fun r hr => (k8.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)).trans (hcs7 r hr)) hM8
    (lo := 0) (z := 8 * (s.gpr .rdx).toNat - (s.gpr .rcx).toNat) (fixed := fixed)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) hlenE
    (fun i hi => ?_) (by simp [upd, proW', proW]) (by simp [upd]) (by simp only [upd]; simp; congr 1; omega)
    (by simp [upd, proW', hel]) (by simp [upd, proW']) (by simp [upd, hfixed])
    (by simp [upd, proW', proW]) (by simp [upd, proW', proW]) (by simp [upd, proW', proW])
    (by simp [upd, proW', proW]) (by simp [upd, proW', proW]) (Nat.zero_le 1) (by omega) ?_ hsl
  · simp only [cpV, Nat.add_zero]
    rw [ifp ⟨Nat.le_add_right _ _, by omega⟩, Nat.add_sub_cancel_left, hem i hi]
  · rw [chkOut, RsaPss.verifyEncoding_bytes lk.G hG hlenD (by rw [hlenE, hel]) (by rw [← hel]; show lk.G.len + sLen.getD 0 + 2 ≤ _; omega), ← hel]
    simp

include hH K in
/-- `checkEncoding` meets `chkK`, keeping the callee-saved registers, its
return address and MXCSR's control bits. -/
theorem chk_correct (lk : Pbkdf2.Md.X86_64.MgfLink H hH) (s : State) (h : (chkK lk.G).pre s) :
    ∃ t s', Exec isa (checkEncoding H) s t s' ∧ abiPreserved s s' ∧ (chkK lk.G).post s s' := by
  have hp := Pre.of lk.G h
  have hsp : SpSafe (checkEncoding H) := by
    have h' := chk_spAll hH K
    rw [Code.allInstrs_eq] at h'
    intro i hi
    simpa using List.all_eq_true.mp h' i hi
  have hW := X86_64.WP.stackFrame hsp (by have := chk_xd K (H := H); unfold chkStack at this; omega)
    (chk_ok hH K lk h)
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  have hd := chk_xd K (H := H)
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.dRs _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (checkEncoding H).x86_64Depth) (k := 8)
      (by unfold chkStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.RsaPss.X86_64.Chk
