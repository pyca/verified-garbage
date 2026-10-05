import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-!
# RSAES-OAEP on x86-64: the label's hash

`hashLabel H o` writes the label's hash `H(label)` to `scratch + o`
(`hashLabel_ok`): `init`, `update` with the label (from its slots, in the
caller's memory), and `finalize`. The working space changes only within the
hash function's ranges and the digest's 64 bytes at `o`.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off word Scr off_off)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

variable {G : Stream} (hG : StreamOK G)

/-- Where the label is: its slots, and its bytes apart from our working
space and the stack below the frame. -/
structure LabAt (t : State) (F S : Addr) (W : Nat → BitVec 64) (lab : Addr) (labLen : Nat) : Prop where
  hl : W 27 = lab
  hll : W 28 = BitVec.ofNat 64 labLen
  len : labLen < 2 ^ 63
  cov : Covers [⟨lab, labLen⟩] (t.rd ++ t.wr)
  dS : Region.Disjoint ⟨lab, labLen⟩ ⟨S, oRsa⟩
  dK : (below F 16).Disjoint ⟨lab, labLen⟩

theorem LabAt.congr {t t' : State} {F S : Addr} {W W' : Nat → BitVec 64} {lab : Addr} {labLen : Nat}
    (h : LabAt t F S W lab labLen) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (h27 : W' 27 = W 27)
    (h28 : W' 28 = W 28) : LabAt t' F S W' lab labLen :=
  ⟨h27.trans h.hl, h28.trans h.hll, h.len, by rw [hrd, hwr]; exact h.cov, h.dS, h.dK⟩

theorem labA_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {lab : Addr} {labLen : Nat} (A : LabAt u F S W lab labLen) :
    WP isa (.block (scr .rdi oSt ++ [.mov32 .rsi (.imm 0), .mov .rdx (.mem (sp sLab)),
      .mov .rcx (.mem (sp sLabLen))] ++ scr .r8 oW)) u fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 0 ∧ u'.gpr .rdx = lab ∧ u'.gpr .rcx = BitVec.ofNat 64 labLen ∧
      u'.gpr .r8 = off S oW ∧ u'.mem = u.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx, .r8] u u' := by
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 0 ∧ u'.gpr .rdx = lab ∧ u'.gpr .rcx = BitVec.ofNat 64 labLen ∧
      u'.gpr .r8 = off S oW ∧ u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, e, f⟩, k⟩ => ⟨a, b, c, d, e, f, k⟩
  xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sLab) (by decide), L.ld (d := sLabLen) (by decide), hs,
    R.slot (d := sLab) (k := 27) rfl (by decide) A.hl, R.slot (d := sLabLen) (k := 28) rfl (by decide) A.hll,
    VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

theorem labF_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {labLen : Nat} (hll : W 28 = BitVec.ofNat 64 labLen) {o : Nat} (ho : o < 2 ^ 31) :
    WP isa (.block (scr .rdi oSt ++ [.mov .rsi (.mem (sp sLabLen))] ++ scr .rdx o ++ scr .rcx oW)) u fun u' =>
      u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 labLen ∧ u'.gpr .rdx = off S o ∧
      u'.gpr .rcx = off S oW ∧ u'.mem = u.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] u u' := by
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 labLen ∧ u'.gpr .rdx = off S o ∧ u'.gpr .rcx = off S oW ∧
      u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, e⟩, k⟩ => ⟨a, b, c, d, e, k⟩
  xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sLabLen) (by decide), hs,
    R.slot (d := sLabLen) (k := 28) rfl (by decide) hll,
    VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide), VG.Proof.MlKem.X86_64.sx_ofNat ho,
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

/-- The ranges the label's hashing writes, with its digest at `o`. -/
def labR (o : Nat) : List (Nat × Nat) := [(oSt, 256), (o, 64), (oW, 2048)]

include hG in
theorem hashLabel_ok {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x) {u : State} {F S : Addr}
    (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {lab : Addr} {labLen : Nat}
    (A : LabAt u F S W lab labLen) {o : Nat} (ho : o = oDig ∨ o = oLh) :
    WP isa (hashLabel G o) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      ∃ V', Rep u'.mem F S V' W ∧ (∀ x, ¬ inR (labR o) x → V' x = V x) ∧
        ∀ i < G.D, V' (o + i) = (Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)).getD i 0 := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  have hlen := A.len
  unfold hashLabel seqs seqs seqs seqs seqs
  refine WP.seq (WP.mono (scr_ok L (d := .rdi) (by decide) (o := oSt) (by decide)) fun u1 ⟨hdi1, hm1, k1⟩ => ?_)
  have L1 : Lay u1 F S := L.congr (k1.gpr (by decide)) k1.2.2 (by rw [hm1])
  have R1 : Rep u1.mem F S V W := hm1 ▸ R
  refine WP.seq (WP.mono (init_ok hG L1 R1 hdi1) fun u2 ⟨L2, rd2, wr2, cs2, R2, hF2, hr2⟩ => ?_)
  obtain ⟨V2, R2, hV2, -⟩ := Rep.ex R2
  have A2 : LabAt u2 F S W lab labLen := A.congr (rd2.trans k1.2.1) (wr2.trans k1.2.2) rfl rfl
  refine WP.seq (WP.mono (labA_ok L2 R2 A2) fun u3 ⟨hdi3, hsi3, hdx3, hcx3, h83, hm3, k3⟩ => ?_)
  have L3 : Lay u3 F S := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W := hm3 ▸ R2
  have A3 : LabAt u3 F S W lab labLen := A2.congr k3.2.1 k3.2.2 rfl rfl
  refine WP.seq (WP.mono (updExt_ok hG L3 R3 A3.len A3.cov A3.dS A3.dK hdi3 hdx3 hcx3 h83)
    fun u4 ⟨L4, rd4, wr4, cs4, R4, _, hr4⟩ => ?_)
  have hR4 := hr4 [] (hm3 ▸ hr2) (by rw [hsi3]; rfl)
  rw [List.nil_append, hm3] at hR4
  obtain ⟨V4, R4, hV4, -⟩ := Rep.ex R4
  refine WP.seq (WP.mono (labF_ok L4 R4 A.hll (o := o) (by rcases ho with rfl | rfl <;> decide))
    fun u5 ⟨hdi5, hsi5, hdx5, hcx5, hm5, k5⟩ => ?_)
  have L5 : Lay u5 F S := L4.congr (k5.gpr (by decide)) k5.2.2 (by rw [hm5])
  have R5 : Rep u5.mem F S V4 W := hm5 ▸ R4
  refine WP.mono (fin_ok hG L5 R5 (o := o) (Or.inr hoo) hdi5 hdx5 hcx5) fun u6 ⟨L6, rd6, wr6, cs6, R6, hr6⟩ => ?_
  have hlb : (Spec.Rsa.bytesAt u2.mem lab labLen).length = labLen := by
    simp [Spec.Rsa.bytesAt]
  have hdig := hr6 _ (hm5 ▸ hR4) (by rw [hlb]; omega) (by rw [hsi5, hlb])
  have hlab : Spec.Rsa.bytesAt u2.mem lab labLen = Spec.Rsa.bytesAt u.mem lab labLen := by
    rw [← hm1]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hF2.bytes (R := ⟨lab, labLen⟩) (fun r hr => ?_) (by show labLen ≤ 2 ^ 64; omega)
      (List.mem_range.mp hi)
    rcases List.mem_append.mp hr with hr | hr
    · simp only [regs, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
      have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
      have hs : Region.Sub ⟨off S oSt, G.S⟩ ⟨S, oRsa⟩ := Offset.sub_base S h1
      exact A.dS.sub_right hs
    · rw [List.mem_singleton.mp hr]; exact A.dK.symm
  obtain ⟨V6, R6, hV6, hV6'⟩ := Rep.ex R6
  refine ⟨L6, rd6.trans (k5.2.1.trans (rd4.trans (k3.2.1.trans (rd2.trans k1.2.1)))),
    wr6.trans (k5.2.2.trans (wr4.trans (k3.2.2.trans (wr2.trans k1.2.2)))), fun r hr => ?_, V6, R6,
    fun x hx => ?_, fun i hi => ?_⟩
  · rw [cs6 r hr, keep_cs' k5 (cs_disj _ (by decide)) r hr, cs4 r hr, keep_cs' k3 (cs_disj _ (by decide)) r hr,
      cs2 r hr, keep_cs' k1 (cs_disj _ (by decide)) r hr]
  · simp only [labR, inR_cons, inR_nil, or_false] at hx
    rw [hV6 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV4 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega)]
  · rw [hV6' _ (by simp only [inR_cons, inR_nil, or_false]; omega), hdig i hi, hHh, hlab]

end VG.Proof.RsaOaep.X86_64
