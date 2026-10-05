import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyButterfly

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (XOnly)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q Zq)

def foldL (x : BitVec 32) : BitVec 32 := x - ((x >>> 23) <<< 23) + ((x >>> 23) <<< 13) - (x >>> 23)

theorem foldL_toNat (x : BitVec 32) (hx : x.toNat < 17 * q) :
    (foldL x).toNat = x.toNat % 8388608 + x.toNat / 8388608 * 8191 := by
  simp only [foldL, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change x.toNat < 17 * 8380417 at hx
  omega

theorem reduceL_toNat (x : BitVec 32) (hx : x.toNat < 17 * q) :
    (csubL (foldL x)).toNat = x.toNat % q := by
  have hf := final_reduce hx
  rw [csubL_toNat (by rw [foldL_toNat x hx]; exact hf.1), foldL_toNat x hx, condSub_eq hf.1, hf.2]

theorem dword_psrld (a : BitVec 128) (k : BitVec 8) (hk : k.toNat < 32) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld a k) i = dword a i >>> k.toNat := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XShiftOp.eval, show ¬ 31 < k.toNat by omega]

theorem dword_pslld (a : BitVec 128) (k : BitVec 8) (hk : k.toNat < 32) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld a k) i = dword a i <<< k.toNat := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XShiftOp.eval, show ¬ 31 < k.toNat by omega]

def foldV (x : BitVec 128) : BitVec 128 :=
  let t := XShiftOp.eval .psrld x 23
  XBinOp.eval .psubd (XBinOp.eval .paddd
    (XBinOp.eval .psubd x (XShiftOp.eval .pslld t 23)) (XShiftOp.eval .pslld t 13)) t

theorem dword_foldV (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (foldV x) i = foldL (dword x i) := by
  rw [foldV, dword_psubd _ _ hi, dword_paddd _ _ hi, dword_psubd _ _ hi,
    dword_pslld _ _ (by decide) hi, dword_pslld _ _ (by decide) hi, dword_psrld _ _ (by decide) hi]
  rfl

theorem reduce_ok {s : State} (hc : Arith.VConsts s) {a : Nat → Word}
    (ha : DLanes (s.xmm .xmm0) a) (hb : ∀ i < 4, (a i).val < 17 * q) :
    WP isa (.block reduceLazy) s fun s' =>
      Arith.DLanes (s'.xmm .xmm0) (fun i => residue (a i)) ∧ XOnly [.xmm0, .xmm1, .xmm2] s s' := by
  simp only [reduceLazy, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q]
  refine ⟨?_, by xonly⟩
  change Arith.DLanes (csubV (foldV (s.xmm .xmm0))) _
  intro i hi
  rw [dword_csubV _ hi, dword_foldV _ hi, reduceL_toNat _ (by rw [ha i hi]; exact hb i hi), ha i hi]
  rfl

end VG.Proof.MlDsa.X86_64.Arith.Lazy
