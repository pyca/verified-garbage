import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf

/-!
# RSAES-OAEP on AArch64: the label's hash

As on x86-64 (`Proof/RsaOaep/X86_64/Label.lean`): `hashLabel H o` writes
the label's hash `H(label)` to `scratch + o` (`hashLabel_ok`): `init`,
`update` with the label (from its slots, in the caller's memory), and
`finalize`. The working space changes only within the hash function's
ranges and the digest's 64 bytes at `o`.
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Stream Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)

/-- Where the label is: its slots, and its bytes apart from our working
space, the frame and the stack below the frame. -/
structure LabAt (t : State) (F S : Addr) (W : Nat → BitVec 64) (lab : Addr) (labLen : Nat) : Prop where
  hl : W 25 = lab
  hll : W 26 = BitVec.ofNat 64 labLen
  len : labLen < 2 ^ 64
  cov : Covers [⟨lab, labLen⟩] (t.rd ++ t.wr)
  dS : Region.Disjoint ⟨lab, labLen⟩ ⟨S, oRsa⟩
  dF : Region.Disjoint ⟨lab, labLen⟩ ⟨F, frameBytes⟩
  dK : (below F 16).Disjoint ⟨lab, labLen⟩

theorem LabAt.congr {t t' : State} {F S : Addr} {W W' : Nat → BitVec 64} {lab : Addr} {labLen : Nat}
    (h : LabAt t F S W lab labLen) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (h25 : W' 25 = W 25)
    (h26 : W' 26 = W 26) : LabAt t' F S W' lab labLen :=
  ⟨h25.trans h.hl, h26.trans h.hll, h.len, by rw [hrd, hwr]; exact h.cov, h.dS, h.dF, h.dK⟩

theorem labA_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {lab : Addr} {labLen : Nat} (A : LabAt u F S W lab labLen) (ws : List Region) :
    WP isa (.block (scr .x0 oSt ++ ([.movz .x .x1 0 0, .ldrSp .x2 sLab, .ldrSp .x3 sLabLen] : List Instr) ++
      scr .x4 oW)) u fun u' => Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = off S oSt ∧
      u'.gpr .x1 = BitVec.ofNat 64 0 ∧ u'.gpr .x2 = lab ∧ u'.gpr .x3 = BitVec.ofNat 64 labLen ∧
      u'.gpr .x4 = off S oW := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h200 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 200) 8 := L.ld (d := 200) (by decide)
  have h208 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 208) 8 := L.ld (d := 208) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have hl := R.rd8 (d := 200) (k := 25) rfl (by decide) A.hl
  have hll := R.rd8 (d := 208) (k := 26) rfl (by decide) A.hll
  oaep_run [scr, Mgf1.scr, lay, sScr, sLab, sLabLen, oSt, oW, h96, h200, h208, L.sp, hs, hl, hll]
  oaep_fin

theorem labF_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {labLen : Nat} (hll : W 26 = BitVec.ofNat 64 labLen) {o : Nat} (ho : o < 4096)
    (ws : List Region) :
    WP isa (.block (scr .x0 oSt ++ ([.ldrSp .x1 sLabLen] : List Instr) ++ scr .x2 o ++ scr .x3 oW)) u fun u' =>
      Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = off S oSt ∧ u'.gpr .x1 = BitVec.ofNat 64 labLen ∧
      u'.gpr .x2 = off S o ∧ u'.gpr .x3 = off S oW := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h208 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 208) 8 := L.ld (d := 208) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have hl := R.rd8 (d := 208) (k := 26) rfl (by decide) hll
  oaep_run [scr, Mgf1.scr, lay, sScr, sLabLen, oSt, oW, h96, h208, L.sp, hs, hl, ho]
  oaep_fin

/-- The ranges the label's hashing writes, with its digest at `o`. -/
def labR (o : Nat) : List (Nat × Nat) := [(oSt, 256), (o, 64), (oW, 1072)]

variable {G : Hash} (hG : StreamOK G.stream)

include hG in
theorem hashLabel_ok {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x) {u : State} {F S : Addr}
    (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {lab : Addr} {labLen : Nat}
    (A : LabAt u F S W lab labLen) {o : Nat} (ho : o = oDig ∨ o = oLh) :
    WP isa (hashLabel G o) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      ∃ V', Rep u'.mem F S V' W ∧ (∀ x, ¬ inR (labR o) x → V' x = V x) ∧
        ∀ i < G.D, V' (o + i) = (Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)).getD i 0 := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have eD : G.stream.D = G.D := rfl
  rw [eD] at hzDF hzD
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  have hlen := A.len
  unfold hashLabel seqs seqs seqs seqs seqs
  refine WP.seq (WP.mono (initArgs_ok L []) fun u1 ⟨S1, hm1, x01⟩ => ?_)
  have L1 : Lay u1 F S := L.congr S1.sp S1.wr (by rw [hm1])
  have R1 : Rep u1.mem F S V W := hm1 ▸ R
  refine WP.seq (WP.mono (init_ok hG L1 R1 x01 []) fun u2 ⟨L2, S2, R2, hr2⟩ => ?_)
  obtain ⟨V2, R2, hV2, -⟩ := Rep.ex R2
  have A2 : LabAt u2 F S W lab labLen := A.congr (S2.rd.trans S1.rd) (S2.wr.trans S1.wr) rfl rfl
  refine WP.seq (WP.mono (labA_ok L2 R2 A2 []) fun u3 ⟨S3, hm3, x03, x13, x23, x33, x43⟩ => ?_)
  have L3 : Lay u3 F S := L2.congr S3.sp S3.wr (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W := hm3 ▸ R2
  have A3 : LabAt u3 F S W lab labLen := A2.congr S3.rd S3.wr rfl rfl
  refine WP.seq (WP.mono (updExt_ok hG L3 R3 A3.len A3.cov A3.dS A3.dK x03 x23 x33 x43 [])
    fun u4 ⟨L4, S4, R4, hr4⟩ => ?_)
  have hR4 := hr4 [] (hm3 ▸ hr2) (by rw [x13]; rfl)
  rw [List.nil_append, hm3] at hR4
  obtain ⟨V4, R4, hV4, -⟩ := Rep.ex R4
  refine WP.seq (WP.mono (labF_ok L4 R4 A.hll (o := o) (by rcases ho with rfl | rfl <;> decide) [])
    fun u5 ⟨S5, hm5, x05, x15, x25, x35⟩ => ?_)
  have L5 : Lay u5 F S := L4.congr S5.sp S5.wr (by rw [hm5])
  have R5 : Rep u5.mem F S V4 W := hm5 ▸ R4
  refine WP.mono (fin_ok hG L5 R5 (o := o) (Or.inr hoo) x05 x25 x35 []) fun u6 ⟨L6, S6, R6, hr6⟩ => ?_
  have hlb : (Spec.Rsa.bytesAt u2.mem lab labLen).length = labLen := by
    simp [Spec.Rsa.bytesAt]
  have hdig := hr6 _ (hm5 ▸ hR4) (by rw [hlb]; omega) (by rw [x15, hlb])
  have hlab : Spec.Rsa.bytesAt u2.mem lab labLen = Spec.Rsa.bytesAt u.mem lab labLen := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (S1.trans S2).frame.bytes (R := ⟨lab, labLen⟩) (fun r hr => ?_)
      (by show labLen ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [A.dF, A.dS, A.dK.symm]
  obtain ⟨V6, R6, hV6, hV6'⟩ := Rep.ex R6
  refine ⟨L6, S1.trans (S2.trans (S3.trans (S4.trans (S5.trans S6)))), V6, R6, fun x hx => ?_, fun i hi => ?_⟩
  · simp only [labR, inR_cons, inR_nil, or_false] at hx
    have : hG.Wb ≤ 1072 := hzW
    rw [hV6 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV4 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega)]
  · rw [hV6' _ (by simp only [inR_cons, inR_nil, or_false]; omega), hdig i hi, hHh, hlab]

end VG.Proof.RsaOaep.AArch64
