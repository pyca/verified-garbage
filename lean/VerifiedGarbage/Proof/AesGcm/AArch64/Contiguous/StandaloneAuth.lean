module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.PaddedCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralBodyCT
public import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Padded
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralBodyCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.Spec.Gcm VG.Proof.Gcm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone (padded)
variable {wn n j : Nat} {C St W SP O : Addr} {s : State} {k : Reg → Addr}

private theorem pad_message (a c : List Byte) : padA (padA a ++ c) = VG.Proof.Gcm.padded a c := by
  cases c with
  | nil =>
    simp only [List.append_nil,VG.Proof.Gcm.padded,ghashInput,↓reduceIte]
    rw [show padA (padA a) = padA a by
      change padA a ++ zeros (padLen (padA a).length) = padA a; rw [padLen_of_mod (length_padA_mod a)]; simp [zeros]]
  | cons b bs =>
    rw [VG.Proof.Gcm.padded,ghashInput_of_ne (by simp)]

theorem auth_ok (L : Lay wn C St W) (v : GcmImpl) (e : Env wn C St W SP s) (keep : Kept k s)
    (dst : DataOk wn St W s O n) (le : 16*j ≤ n) (endPtr : s.gpr .x26 = O+BitVec.ofNat 64 n)
    (slot : s.mem.readW (W+352) 64 = O+BitVec.ofNat 64 (16*j)) (aad : List Byte) (H : Block)
    (key : blockAt s.mem (C+BitVec.ofNat 64 240) = H)
    (acc : blockAt s.mem (St+BitVec.ofNat 64 16) =
      ghashFrom H (ghash H (blocks (padA aad))) (blocksAt s.mem O j)) :
    WP isa (.seq (.block DirectGather.suffixStart) (VG.Impl.AesGcm.AArch64.Contiguous.Standalone.padded v.callees)) s fun z =>
      Env wn C St W SP z ∧ Kept k z ∧ blockAt z.mem (St+BitVec.ofNat 64 16) =
        ghash H (blocks (VG.Proof.Gcm.padded aad (bytesAt s.mem O n))) ∧
      Frame (absFrame St W 16 ++ tFrame St W 16) s.mem z.mem := by
  refine WP.seq ((DirectGather.suffixStart_ok e le dst.lt endPtr slot).mono fun u ⟨src,len,r⟩ => ?_)
  let pre := padA aad ++ bytesAt s.mem O (16*j)
  have aligned : pre.length%16 = 0 := by
    change ((padA aad ++ _).length % 16) = 0
    rw [List.length_append,length_bytesAt,Nat.add_mod,length_padA_mod,Nat.mul_mod_right]
  have prior : Absorbed u.mem (St+BitVec.ofNat 64 16) (St+BitVec.ofNat 64 32) H pre := by
    constructor
    · rw [r.mem,whole_of_mod aligned,List.take_of_length_le (Nat.le_refl _),acc,blocksAt_eq]
      rw [show blocks pre = blocks (padA aad) ++ blocks (bytesAt s.mem O (16*j)) from blocks_append (length_padA_mod aad)]
      exact (ghashFrom_append ..).symm
    · rw [aligned,whole_of_mod aligned,List.drop_of_length_le (Nat.le_refl _)]
      rfl
  refine (padded_ok L v (e.of_regs r) (keep.of_others r.others) src len
    ((dst.drop le).of_eq r.rd r.wr) (r.mem ▸ key) aligned prior).mono fun z out => ?_
  refine ⟨out.env,out.kept,?_,r.mem ▸ out.frame⟩
  have split : bytesAt s.mem O n = bytesAt s.mem O (16*j) ++ bytesAt s.mem (O+BitVec.ofNat 64 (16*j)) (n-16*j) :=
    (congrArg (bytesAt s.mem O) (show n=16*j+(n-16*j) by omega)).trans (bytesAt_add ..)
  have txt : pre ++ bytesAt u.mem (O+BitVec.ofNat 64 (16*j)) (n-16*j) = padA aad ++ bytesAt s.mem O n := by
    rw [r.mem,split]; exact List.append_assoc ..
  have h := out.hash.1
  change _ = ghash H (blocks ((padA _).take (whole (padA _).length))) at h
  rw [txt,pad_message,whole_of_mod (length_padded ..),List.take_of_length_le (Nat.le_refl _)] at h
  exact h

theorem auth_rel {t : State} (L : Lay wn C St W) (v : GcmImpl)
    (ea : Env wn C St W SP s) (eb : Env wn C St W SP t)
    (da : DataOk wn St W s O n) (db : DataOk wn St W t O n) (le : 16*j ≤ n)
    (oa : s.gpr .x26 = O+BitVec.ofNat 64 n) (ob : t.gpr .x26 = O+BitVec.ofNat 64 n)
    (pa : s.mem.readW (W+352) 64 = O+BitVec.ofNat 64 (16*j)) (pb : t.mem.readW (W+352) 64 = O+BitVec.ofNat 64 (16*j)) :
    RelCT isa (Eq2 s t) (.seq (.block DirectGather.suffixStart) (VG.Impl.AesGcm.AArch64.Contiguous.Standalone.padded v.callees)) TT := by
  refine rel_seq (rel_taint [.x19] (ea.sp.trans eb.sp.symm) (by agree_tac [ea.x19,eb.x19]) ⟨_,by taint_decide⟩)
    (DirectGather.suffixStart_ok ea le da.lt oa pa) (DirectGather.suffixStart_ok eb le db.lt ob pb) ?_
  rintro _ _ ⟨x,y,r⟩ ⟨z,w,q⟩
  exact padded_rel L v (ea.of_regs r) (eb.of_regs q) x z y w ((da.drop le).of_eq r.rd r.wr) ((db.drop le).of_eq q.rd q.wr)

theorem count_eq {j' : Nat} (le : 16*j≤n) (le' : 16*j'≤n) (bound : n<2^64)
    (h : O+BitVec.ofNat 64 (16*j) = O+BitVec.ofNat 64 (16*j')) : j=j' := by
  have eq := congrArg (fun p : Addr => (p-O).toNat) h
  simp only [Offset.add_sub_cancel_left] at eq
  rw [toNat_ofNat_of_lt (by omega),toNat_ofNat_of_lt (by omega)] at eq
  omega

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
