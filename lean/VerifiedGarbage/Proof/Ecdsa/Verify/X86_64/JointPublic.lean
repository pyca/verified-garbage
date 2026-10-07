import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Timing
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming

/-! Equal public verification inputs determine both scalars and every joint-window input field. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)
open VG.Impl.Ecdsa.Verify.X86_64 (U V EM')

structure JointPublic (c : Cfg) (d : CombData) (a b : State) : Prop where
  regs : X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx]) a b
  sym : a.syms d.tsym=b.syms d.tsym
  tag : a.mem (a.gpr .rdi)=b.mem (b.gpr .rdi)
  x : keyX c a=keyX c b
  y : keyY c a=keyY c b
  digest : dig c a=dig c b
  r : sigR c a=sigR c b
  s : sigS c a=sigS c b

def publicV (c : Cfg) (s : State) : Nat :=
  (Fin.ofNat c.C.n (sigR c s)*Fin.ofNat c.C.n (sigS c s)^(c.C.n-2)).val

theorem mid_publicV {c : Cfg} {s₀ s : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid c s₀ base g s) : sv c base s V=publicV c s₀ := by
  have he := congrArg Fin.val h.v
  simpa only [Fin.val_ofNat,Nat.mod_eq_of_lt h.v_lt,publicV] using he

theorem JointPublic.key {c : Cfg} {d : CombData} {a b : State} (h : JointPublic c d a b) :
    KeyOk c a=KeyOk c b := by
  simp only [KeyOk,h.tag,h.x,h.y]

theorem JointPublic.u {c : Cfg} {d : CombData} {a b : State} (h : JointPublic c d a b) :
    publicU c a=publicU c b := by simp only [publicU,h.digest,h.s]

theorem JointPublic.v {c : Cfg} {d : CombData} {a b : State} (h : JointPublic c d a b) :
    publicV c a=publicV c b := by simp only [publicV,h.r,h.s]

private theorem eq_of_toM_eq {m R x y : Nat} [NeZero m] (hm : UnitMod m R)
    (hx : x<m) (hy : y<m) (h : toM m R x=toM m R y) : x=y := by
  have unit := mul_rinv hm
  have he : Fin.ofNat m x=Fin.ofNat m y := by unfold toM at h; grind
  have hv := congrArg Fin.val he
  simpa only [Fin.val_ofNat,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using hv

theorem jointMid_samefields {c : Cfg} {d : CombData} (hc : CfgOk c)
    {s₀ t₀ s t : State} {base : Addr} {g h : Reg → BitVec 64}
    (pub : JointPublic c d s₀ t₀) (hs : Mid c s₀ base g s) (ht : Mid c t₀ base h t) :
    ∀ x∈winRo (c.winCfg PX PY BP),tmv c.C c.n base t x=tmv c.C c.n base s x := by
  have em : sv c base t EM'=sv c base s EM' :=
    eq_of_toM_eq (unitMod_pow_two hc.n_odd _) ht.em_lt hs.em_lt
      (ht.em.trans ((congrArg (Fin.ofNat c.C.n) pub.digest).symm.trans hs.em.symm))
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
  · change toM _ _ (wordsVal t.mem base (c.sl AP) c.n)=toM _ _ (wordsVal s.mem base (c.sl AP) c.n)
    rw [ht.fixed.ap,hs.fixed.ap]
  · exact congrArg (fun x => toM c.C.p (2^(64*c.n)) x) em
  · change toM _ _ (wordsVal t.mem base (c.sl ZERO) c.n)=toM _ _ (wordsVal s.mem base (c.sl ZERO) c.n)
    rw [ht.fixed.zero,hs.fixed.zero]
  · change toM _ _ (sv c base t PX)=toM _ _ (sv c base s PX)
    simp only [ht.px,hs.px,pub.key,pub.x]
  · change toM _ _ (sv c base t PY)=toM _ _ (sv c base s PY)
    simp only [ht.py,hs.py,pub.key,pub.y]
  · change toM _ _ (wordsVal t.mem base (c.sl ONEP) c.n)=toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)
    rw [ht.fixed.onep,hs.fixed.onep]

theorem jointMid_field_pair {c : Cfg} {j : Joint.Cfg} {d : CombData} (hc : CfgOk c)
    (hK : j.K=c.winCfg PX PY BP) (hnp : c.C.n≤c.C.p)
    {s₀ t₀ s t : State} {base : Addr} {g h : Reg → BitVec 64}
    (pub : JointPublic c d s₀ t₀) (hs : Mid c s₀ base g s) (ht : Mid c t₀ base h t) :
    FieldPair j.K.M base size c.C.p (·∈nafSlots j.K) (winRo j.K) (tmv c.C j.K.M.n base s) s t := by
  have is := jointMid_field hc hK hnp hs
  have it := jointMid_field hc hK hnp ht
  refine ⟨is,{it with val := ?_}⟩
  intro x hx
  rw [hK] at hx ⊢
  exact jointMid_samefields hc pub hs ht x hx

end VG.Proof.Ecdsa.Verify.X86_64
