import VerifiedGarbage.Proof.RsaOaep.X86_64.Loops
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls

/-!
# RSAES-OAEP on x86-64: calling the streaming hash functions

The streaming `init`, `update` and `finalize` of a hash function (a
`StreamOK`, `Proof/Pbkdf2/Md/X86_64/Calls.lean`), called from the frame on
the state at `scratch + oSt`, with the working space at `scratch + oW` and
the digest to `scratch + o`: what each leaves of the frame and the working
space (`Lay`, `Rep`, with the ranges it writes read again), and what it
computes. A register `d` is set to `scratch + o` by `scr_ok`.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off word Scr off_off)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK After init_call upd_call fin_call UpdArgs FinArgs)

/-- `scratch + o` into `d`. -/
theorem scr_ok {t : State} {F S : Addr} (L : Lay t F S) {d : Reg} (hd : d ≠ .rsp) {o : Nat} (ho : o < 2 ^ 31) :
    WP isa (.block (scr d o)) t fun t' => t'.gpr d = off S o ∧ t'.mem = t.mem ∧ Keep [d] t t' := by
  refine WP.mono (WP.keep [d] (Q := fun t' => t'.gpr d = off S o ∧ t'.mem = t.mem) ?_ ?_) fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  · have hl := L.ld (d := sScr) (by decide)
    have hs := L.slot
    simp only [Bignum.X86_64.word] at hs
    xrun [scr, Impl.Mgf1.X86_64.scr, lay, ea_sp, L.rsp, hl, hs, VG.Proof.MlKem.X86_64.sx_ofNat ho]
  · cases d <;> first | exact absurd rfl hd | rfl

/-- What a call leaves of the frame: `Lay`, and the view of memory with the
ranges `rgs` it may write read again. -/
theorem Lay.after_call {t t' : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {rgs : List (Nat × Nat)} (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa)
    (hF : Frame (regs S rgs ++ [retR F]) t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) (hwr : t'.wr = t.wr) :
    Lay t' F S ∧ Rep t'.mem F S (fun o => if inR rgs o then t'.mem (off S o) else V o) W := by
  have R' := R.frame L.geo hrg hF
  refine ⟨L.congr hsp hwr ?_, R'⟩
  rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, R'.fr 14 (by decide), R.fr 14 (by decide)]

variable {G : Stream} (hG : StreamOK G)

include hG in
theorem sizes : G.S ≤ 256 ∧ G.F ≤ 64 ∧ hG.Wb ≤ 2048 ∧ G.D ≤ G.F ∧ 0 < G.D :=
  ⟨hG.hSB, hG.hF, by have := hG.hWb; have := hG.hW; omega, hG.hDF, hG.hD0⟩

/-- A range of our working space and the 16 bytes below the frame are
apart. -/
theorem Lay.stk {t : State} {F S : Addr} (L : Lay t F S) {o n : Nat} (h : o + n ≤ oRsa) :
    (below (t.gpr .rsp) 16).Disjoint ⟨off S o, n⟩ := by
  rw [L.rsp]; exact L.dRS.sub_right (Offset.sub_base S h)

/-- Two ranges of our working space that do not overlap. -/
theorem sdis (S : Addr) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ oRsa) (hb : b + k ≤ oRsa) :
    Region.Disjoint ⟨off S a, n⟩ ⟨off S b, k⟩ :=
  Offset.disjoint S h (by unfold oRsa at ha; omega) (by unfold oRsa at hb; omega)

/-- After a call that keeps `rsp` and the callee-saved registers. -/
theorem keep_cs {t t' : State} (h : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : t'.gpr .rsp = t.gpr .rsp :=
  h .rsp (by decide)

/-! ## `init` -/

include hG in
theorem init_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (hdi : t.gpr .rdi = off S oSt) :
    WP isa (.call G.initN G.initC) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S)] o then t'.mem (off S o) else V o) W ∧
      hG.SH.Repr t'.mem (off S oSt) [] := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  refine init_call hG hdi (L.cov h1) (L.stk h1) fun t' A hr => ?_
  obtain ⟨L', R'⟩ := L.after_call R (rgs := [(oSt, G.S)])
    (by simp only [List.mem_singleton]; rintro p rfl; exact h1)
    (by have := A.frame; rw [L.rsp] at this; exact this) (keep_cs A.cs) A.wr
  exact ⟨L', A.rd, A.wr, A.cs, R', hr⟩

/-! ## `update` -/

include hG in
/-- `update` of the state with the `len` bytes at `scratch + a`, after
`cnt` bytes, from the arguments in `rdi`, `rsi`, `rdx`, `rcx`, `r8`. -/
theorem upd_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + G.S ≤ a) (hwa : a + len ≤ oW ∨ oW + hG.Wb ≤ a)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S a) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oW) :
    WP isa (.call G.updN G.updC) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S), (oW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .rsi = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ (List.range len).map fun i => V (a + i))) := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega
  have args : UpdArgs hG t (off S oSt) (off S a) (off S oW) len :=
    { rdi := hdi, rdx := hdx
      rcx := by rw [hcx, BitVec.toNat_ofNat]; unfold oRsa at ha; omega
      r8 := h8
      cd := Covers.right (L.cov ha)
      cw := Covers.pair (L.cov h1) (L.cov h2)
      st_sc := sdis S (Or.inl hsw) h1 h2
      d_st := sdis S hda ha h1
      d_sc := sdis S hwa ha h2
      stk_st := L.stk h1, stk_d := L.stk ha, stk_sc := L.stk h2 }
  refine upd_call hG args (by unfold oRsa at ha; omega) fun t' A hr => ?_
  obtain ⟨L', R'⟩ := L.after_call R (rgs := [(oSt, G.S), (oW, hG.Wb)])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl) <;> with_reducible assumption)
    (by have := A.frame; rw [L.rsp] at this; exact this) (keep_cs A.cs) A.wr
  refine ⟨L', A.rd, A.wr, A.cs, R', fun m hm hc => ?_⟩
  have e : Spec.Sha256.bytesAt t.mem (off S a) len = (List.range len).map fun i => V (a + i) := by
    simp only [Spec.Sha256.bytesAt]
    exact List.map_congr_left fun i hi => by
      rw [off_plus]; exact R.scr _ (by have := List.mem_range.mp hi; omega)
  rw [← e]; exact hr m hm hc

/-! ## `finalize` -/

include hG in
/-- `finalize` of the state to `scratch + o`, from the arguments in `rdi`,
`rsi`, `rdx`, `rcx`. -/
theorem fin_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {o : Nat} (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S o) (hcx : t.gpr .rcx = off S oW) :
    WP isa (.call G.finN G.finC) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun x => if inR [(oSt, G.S), (o, G.F), (oW, hG.Wb)] x then t'.mem (off S x) else V x) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → m.length < 2 ^ 64 → t.gpr .rsi = BitVec.ofNat 64 m.length →
        ∀ i < G.D, t'.mem (off S (o + i)) = (hG.SH.H.hash m).getD i 0) := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have h3 : o + G.F ≤ oRsa := by unfold oSt oW oRsa at *; omega
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega
  have args : FinArgs hG t (off S oSt) (off S o) (off S oW) :=
    { rdi := hdi, rdx := hdx, rcx := hcx
      cw := Covers.cons (L.cov h1) (Covers.pair (L.cov h3) (L.cov h2))
      st_o := sdis S (by unfold oSt oW at *; omega) h1 h3
      st_sc := sdis S (Or.inl hsw) h1 h2
      o_sc := sdis S (by unfold oSt oW at *; omega) h3 h2
      stk_st := L.stk h1, stk_o := L.stk h3, stk_sc := L.stk h2 }
  refine fin_call hG args fun t' A hr => ?_
  obtain ⟨L', R'⟩ := L.after_call R (rgs := [(oSt, G.S), (o, G.F), (oW, hG.Wb)])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
    (by have := A.frame; rw [L.rsp] at this; exact this) (keep_cs A.cs) A.wr
  refine ⟨L', A.rd, A.wr, A.cs, R', fun m hm hl hc i hi => ?_⟩
  have e := hr m hm hl hc
  rw [← e, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  simp only [Spec.Sha256.bytesAt, List.getElem?_map, List.getElem?_range (show i < G.F by omega),
    Option.map_some, Option.getD_some, off_off]

end VG.Proof.RsaOaep.X86_64
