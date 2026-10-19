module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Tail

/-! # Vector iteration under sampler memory and permission hypotheses -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure EnvW (w16 : Bool) (N : Nat) (B : Nat → Byte) (bP aP : Addr) (s : State) : Prop extends
    Scalar.LPreW w16 N B bP aP s where
  input16 : ∀t,t+4≤N → InRegions (s.rd++s.wr) (bP+BitVec.ofNat 64 (3*t)) 16
  output16 : ∀i,i+(if w16 then 8 else 4)≤256 → InRegions s.wr (cAddr w16 aP i) 16
  tableRead : ∀mask<256,InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16
  tableData : ∀mask<256,s.mem.read (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16=tableVec mask
  tableDisj : ∀mask<256,(⟨s.gpr .x16+BitVec.ofNat 64 (16*mask),16⟩ : Region).Disjoint (polyRegion aP)

abbrev Env := EnvW false

theorem vector_ok {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (hp : EnvW w16 N B bP aP s₀) (h : Scalar.InvW w16 initial N B bP aP s₀ t s)
    (hc : Constants s) (ht : t+4≤N) (hroom : 8≤(s.gpr .x4).toNat) :
    WP isa (.block (Impl.MlKem.AArch64.Rej8.rejEight w16)) s fun u =>
      Scalar.InvW w16 initial N B bP aP s₀ (t+4) u ∧ Constants u := by
  have hl : (Scalar.LA initial B t).length+8≤256 := by
    rw [h.acc.x4] at hroom
    have := h.acc.len
    omega
  have hb : ∀i<12,s.mem (s.gpr .x2+BitVec.ofNat 64 i)=B (3*t+i) := by
    intro i hi
    rw [h.x2,ptr_add]
    rw [byte_frame h.acc.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact hp.disj)
      (by have := hp.bound; omega) (by omega),hp.buf _ (by omega)]
  refine WP.mono (batch_ok w16 s hc (by rw [h.acc.rd,h.acc.wr,h.x2]; exact hp.input16 t ht)
    hroom (by rw [h.x5]; omega)
    (by rw [h.acc.wr,h.acc.x3]; exact hp.output16 _ (by cases w16 <;> simp <;> omega))
    (fun hw => by
        subst hw
        rw [h.acc.wr,h.acc.x3,show cAddr false aP (Scalar.LA initial B t).length+16=
          cAddr false aP ((Scalar.LA initial B t).length+4) from cAddr_add false aP _ 4]
        exact hp.output16 _ (by simp; omega))
    (fun mask hm => by rw [h.acc.rd,h.acc.wr,h.keep.get .x16]; exact hp.tableRead mask hm)
    (fun mask hm => by
      rw [h.keep.get .x16,h.acc.frame.read (r := ⟨s₀.gpr .x16+BitVec.ofNat 64 (16*mask),16⟩)
        (Region.contains_self _ 16)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.tableDisj mask hm)
        (by decide)]
      exact hp.tableData mask hm)) fun u hu => ?_
  refine ⟨batch_invW h hl hc.zero hb hu,?_,?_,?_,?_,?_⟩
  · rw [hu.other .v16 (by decide)]; exact hc.index
  · rw [hu.other .v17 (by decide)]; exact hc.mask
  · intro i hi; rw [hu.other .v19 (by decide)]; exact hc.q i hi
  · intro i hi; rw [hu.other .v20 (by decide)]; exact hc.weights i hi
  · intro i hi; rw [hu.other .v21 (by decide)]; exact hc.zero i hi

end VG.Proof.MlKem.AArch64.Rej8
