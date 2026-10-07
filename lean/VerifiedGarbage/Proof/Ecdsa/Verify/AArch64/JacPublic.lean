import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Timing
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

/-! The Jacobian branches depend on the public signature, digest and public key. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Mont
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

/-- The variable-base multiplication scalar. -/
def publicV (c : Cfg) (s : State) : Nat :=
  (Fin.ofNat c.C.n (sigR c s) * Fin.ofNat c.C.n (sigS c s) ^ (c.C.n-2)).val

theorem mid_publicV {c : Cfg} {s₀ s : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid c s₀ base g s) : VG.Proof.Ecdsa.AArch64.sv c base s V = publicV c s₀ := by
  have he := congrArg Fin.val h.v
  simpa only [Fin.val_ofNat,Nat.mod_eq_of_lt h.v_lt,publicV] using he

/-- Equal public-key buffers determine every input of key validation. -/
theorem publicKey_congr {c : Cfg} {s t : State}
    (h : Spec.Ecdsa.bytesAt s.mem (s.gpr .x0) (1+2*c.C.len) =
      Spec.Ecdsa.bytesAt t.mem (t.gpr .x0) (1+2*c.C.len)) :
    s.mem (s.gpr .x0) = t.mem (t.gpr .x0) ∧ keyX c s = keyX c t ∧ keyY c s = keyY c t := by
  rw [bytesAt_add,bytesAt_add] at h
  obtain ⟨htag,hxy⟩ := List.append_inj h (by simp only [length_bytesAt])
  have ht : s.mem (s.gpr .x0) = t.mem (t.gpr .x0) := by
    simpa [Spec.Ecdsa.bytesAt] using htag
  rw [Nat.two_mul,bytesAt_add,bytesAt_add] at hxy
  obtain ⟨hx,hy⟩ := List.append_inj hxy (by simp only [length_bytesAt])
  refine ⟨ht,congrArg Spec.Weierstrass.ofBytes hx,?_⟩
  have hy' := congrArg Spec.Weierstrass.ofBytes hy
  simpa only [keyY,BitVec.ofNat_add,BitVec.add_assoc] using hy'

/-- The stronger internal relation uses only bytes the existing specification makes public. -/
structure JacPublic (c : Cfg) (s t : State) : Prop where
  ptrs : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3]) s t
  table : s.syms c.tsym = t.syms c.tsym
  key : Spec.Ecdsa.bytesAt s.mem (s.gpr .x0) (1+2*c.C.len) =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x0) (1+2*c.C.len)
  digest : Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) c.C.len =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x1) c.C.len
  sig : Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (2*c.C.len) =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x2) (2*c.C.len)

theorem JacPublic.u {c : Cfg} {s t : State} (h : JacPublic c s t) : publicU c s = publicU c t :=
  publicU_congr h.digest h.sig

theorem JacPublic.signature {c : Cfg} {s t : State} (h : JacPublic c s t) :
    sigR c s = sigR c t ∧ sigS c s = sigS c t := by
  have hs := h.sig
  rw [Nat.two_mul,bytesAt_add,bytesAt_add] at hs
  obtain ⟨hr,hs⟩ := List.append_inj hs (by simp only [length_bytesAt])
  exact ⟨congrArg Spec.Weierstrass.ofBytes hr,congrArg Spec.Weierstrass.ofBytes hs⟩

theorem JacPublic.v {c : Cfg} {s t : State} (h : JacPublic c s t) : publicV c s = publicV c t := by
  rw [publicV,publicV,h.signature.1,h.signature.2]

theorem JacPublic.keyOk {c : Cfg} {s t : State} (h : JacPublic c s t) : KeyOk c s ↔ KeyOk c t := by
  obtain ⟨tag,x,y⟩ := publicKey_congr h.key
  simp only [KeyOk,tag,x,y]

/-- The initialized peer coordinates are equal in the two executions. -/
theorem mid_peer_public {c : Cfg} {s₀ t₀ s t : State} {base : Addr}
    {g₁ g₂ : Reg → BitVec 64} (h : JacPublic c s₀ t₀)
    (hs : Mid c s₀ base g₁ s) (ht : Mid c t₀ base g₂ t) :
    VG.Proof.Weierstrass.AArch64.tmv c.C c.n base s (c.sl VG.Impl.Ecdh.AArch64.PX) =
      VG.Proof.Weierstrass.AArch64.tmv c.C c.n base t (c.sl VG.Impl.Ecdh.AArch64.PX) ∧
    VG.Proof.Weierstrass.AArch64.tmv c.C c.n base s (c.sl VG.Impl.Ecdh.AArch64.PY) =
      VG.Proof.Weierstrass.AArch64.tmv c.C c.n base t (c.sl VG.Impl.Ecdh.AArch64.PY) := by
  obtain ⟨_,x,y⟩ := publicKey_congr h.key
  change toM _ _ _ = toM _ _ _ ∧ toM _ _ _ = toM _ _ _
  rw [hs.px,ht.px,hs.py,ht.py]
  simp only [h.keyOk,x,y]
  exact ⟨True.intro,True.intro⟩

end VG.Proof.Ecdsa.Verify.AArch64
