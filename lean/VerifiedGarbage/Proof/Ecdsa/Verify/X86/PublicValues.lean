import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Main

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86
open VG.Impl.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Proof VG.Proof.Ecdsa.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdh.X86 Spec.Weierstrass

structure VInputEq (c : Cfg) (s t : State) : Prop where
  tag : s.mem (ptr s 0)=t.mem (ptr t 0)
  x : keyX c s=keyX c t
  y : keyY c s=keyY c t
  r : sigR c s=sigR c t
  z : sigS c s=sigS c t

theorem VInputEq.key {c : Cfg} {s t : State} (h : VInputEq c s t) : KeyOk c s=KeyOk c t := by
  simp only [KeyOk,h.tag,h.x,h.y]

structure VPublicValues (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  px_lt : sv c base s PX<c.C.p
  py_lt : sv c base s PY<c.C.p
  px : toM c.C.p (2^(64*c.n)) (sv c base s PX)=
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyX c s₀) else Fin.ofNat c.C.p c.C.gx
  py : toM c.C.p (2^(64*c.n)) (sv c base s PY)=
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyY c s₀) else Fin.ofNat c.C.p c.C.gy
  v_lt : sv c base s V<c.C.n
  v : Fin.ofNat c.C.n (sv c base s V)=
    Fin.ofNat c.C.n (sigR c s₀)*Fin.ofNat c.C.n (sigS c s₀)^(c.C.n-2)

theorem Mid.publicValues {c : Cfg} {s₀ s : State} {base : Addr} (h : Mid c s₀ base s) :
    VPublicValues c s₀ base s := ⟨h.px_lt,h.py_lt,h.px,h.py,h.v_lt,h.v⟩

theorem VPublicValues.transfer {c : Cfg} {s₀ s t : State} {base : Addr}
    (h : VPublicValues c s₀ base s) (he : ∀ i∈[PX,PY,V],sv c base t i=sv c base s i) :
    VPublicValues c s₀ base t := by
  have hx := he PX (by decide)
  have hy := he PY (by decide)
  have hv := he V (by decide)
  exact ⟨by rw [hx]; exact h.px_lt,by rw [hy]; exact h.py_lt,by rw [hx]; exact h.px,
    by rw [hy]; exact h.py,by rw [hv]; exact h.v_lt,by rw [hv]; exact h.v⟩

theorem VPublicValues.rebase {c : Cfg} {s₀ t₀ s : State} {base : Addr}
    (h : VPublicValues c t₀ base s) (he : VInputEq c s₀ t₀) : VPublicValues c s₀ base s := by
  refine ⟨h.px_lt,h.py_lt,?_,?_,h.v_lt,?_⟩
  · simpa only [he.key,he.x] using h.px
  · simpa only [he.key,he.y] using h.py
  · rw [he.r,he.z]; exact h.v

theorem VPublicValues.scalar {c : Cfg} {s₀ s : State} {base : Addr}
    (h : VPublicValues c s₀ base s) : sv c base s V=
      (Fin.ofNat c.C.n (sigR c s₀)*Fin.ofNat c.C.n (sigS c s₀)^(c.C.n-2)).val := by
  have hv := congrArg Fin.val h.v
  simpa only [Fin.val_ofNat,Nat.mod_eq_of_lt h.v_lt] using hv

theorem VPublicValues.point {c : Cfg} (hc : CfgOk c) (hC : Law c.C)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 32} (h : VPublicValues c s₀ base s)
    (hf : Fixed c base g s.mem) :
    Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP))
      (Ecdh.X86.peerPt c (s₀.mem (ptr s₀ 0)=4) (keyX c s₀) (keyY c s₀)) := by
  obtain ⟨_,_,hone⟩ := consts_tmv hc hf
  rw [hone]
  exact Ecdh.X86.peerPt_rep hC _ _ _ h.px h.py

theorem VInputEq.of_bytes {c : Cfg} {s t : State}
    (hp : Spec.Ecdsa.bytesAt s.mem (ptr s 0) (1+2*c.C.len)=
      Spec.Ecdsa.bytesAt t.mem (ptr t 0) (1+2*c.C.len))
    (hs : Spec.Ecdsa.bytesAt s.mem (ptr s 2) (2*c.C.len)=
      Spec.Ecdsa.bytesAt t.mem (ptr t 2) (2*c.C.len)) : VInputEq c s t := by
  rw [peer_bytes,peer_bytes] at hp
  obtain ⟨tag,xy⟩ := List.cons.inj hp
  have xy' := List.append_inj xy (by simp only [length_bytesAt])
  rw [show 2*c.C.len=c.C.len+c.C.len by omega,bytesAt_add,bytesAt_add] at hs
  have rs := List.append_inj hs (by simp only [length_bytesAt])
  exact ⟨tag,congrArg Spec.Weierstrass.ofBytes xy'.1,congrArg Spec.Weierstrass.ofBytes xy'.2,congrArg Spec.Weierstrass.ofBytes rs.1,congrArg Spec.Weierstrass.ofBytes rs.2⟩

end VG.Proof.Ecdsa.Verify.X86
