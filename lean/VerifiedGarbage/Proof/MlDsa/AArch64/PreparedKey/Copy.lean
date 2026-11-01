module

public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Base
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Blocks
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten

/-! # Prepared-key copying preserves the encoded key and cached coefficients -/
-- separate module: this memory-copy proof is shared by preparation and both operations.

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep wp_ldrq wp_strq wp_addImm wp_subImm wp_nil)
open VG.Impl.MlDsa.AArch64.Call (Ptr)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (count_loop ptr_add)
open VG.Proof.MlDsa.Pack (Written)
open VG.Proof.MlDsa.AArch64.Optimized.KeygenPack (written_word)

theorem copyBody_ok (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x1) 16)
    (hout : InRegions s.wr (s.gpr .x0) 16) :
    WP isa (.block Impl.MlDsa.AArch64.PreparedKey.copyBody) s fun t =>
      t.mem = s.mem.writeW (s.gpr .x0) (s.mem.readW (s.gpr .x1) 128) ∧
      t.gpr .x0 = s.gpr .x0 + 16#64 ∧ t.gpr .x1 = s.gpr .x1 + 16#64 ∧
      t.gpr .x2 = s.gpr .x2 - 1#64 ∧ Keep [.x0, .x1, .x2] s t := by
  refine wp_ldrq (a := s.gpr .x1) (by decide) (BitVec.add_zero _) hin fun a ha =>
    wp_strq (a := s.gpr .x0) (by decide)
      (by rw [ha.gpr, BitVec.add_zero]) (by rw [ha.wr]; exact hout) fun b hb =>
    wp_addImm (by decide) fun c hc vc => wp_addImm (by decide) fun d hd vd =>
    wp_subImm (by decide) fun t ht vt => wp_nil ?_
  refine ⟨?_, ?_, ?_, ?_,
    ((((ha.keep (by decide)).trans hb.keep).trans hc.keep).trans hd.keep |>.trans ht.keep).mono (by simp)⟩
  · rw [ht.mem, hd.mem, hc.mem, hb.mem, ha.v, ha.mem]
    simp only [Mem.readW, Mem.writeW, BitVec.setWidth_eq]
  · rw [ht.get .x0, hd.get .x0, vc, hb.gpr, ha.gpr]
  · rw [ht.get .x1, vd, hc.get .x1, hb.gpr, ha.gpr]
  · rw [vt, hd.get .x2, hc.get .x2, hb.gpr, ha.gpr]

theorem copy_core {dst src : Ptr} {n : Nat} (h0 : 0 < n) (hn : n < 2 ^ 28)
    (hd : dst.1 ∈ keptRegs) (hs : src.1 ∈ keptRegs) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (pa s src) (16 * n))
    (hout : InRegions s.wr (pa s dst) (16 * n))
    (hsep : (⟨pa s src, 16 * n⟩ : Region).Disjoint ⟨pa s dst, 16 * n⟩) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy dst src (16 * n)) s fun t =>
      bytesAt t.mem (pa s dst) (16 * n) = bytesAt s.mem (pa s src) (16 * n) ∧
      Frame [⟨pa s dst, 16 * n⟩] s.mem t.mem ∧ Keep [.x0, .x1, .x2] s t := by
  let d := pa s dst
  let a := pa s src
  unfold Impl.MlDsa.AArch64.PreparedKey.copy
  rw [ite_eq_right (by omega), show 16 * n / 16 = n by omega]
  refine WP.seq (WP.mono (Sign.copyGlue_ok (n := n) hd hs s)
    fun u ⟨⟨h1, h2, h3⟩, ku⟩ => ?_)
  refine WP.mono (count_loop (cr := .x2) (n := n) h0 (fun k v =>
    v.gpr .x0 = d + BitVec.ofNat 64 (16 * k) ∧
    v.gpr .x1 = a + BitVec.ofNat 64 (16 * k) ∧
    v.gpr .x2 = BitVec.ofNat 64 (n - k) ∧ Keep [.x0, .x1, .x2] s v ∧
    Frame [⟨d, 16 * n⟩] s.mem v.mem ∧
    (∀ j < 16 * k, v.mem (d + BitVec.ofNat 64 j) = s.mem (a + BitVec.ofNat 64 j)))
    (fun k hk v ⟨e0, e1, e2, kv, hf, hb⟩ => ?_) ?_)
    fun t ⟨_, _, _, kt, hf, hb⟩ => ?_
  · refine WP.mono (copyBody_ok v ?_ ?_) fun t ⟨hm, t0, t1, t2, kt⟩ => ?_
    · rw [kv.rd, kv.wr, e1]
      exact inRegions_sub hin (by omega) (by omega)
    · rw [kv.wr, e0]
      exact inRegions_sub hout (by omega) (by omega)
    · have hw : Written v.mem t.mem (d + BitVec.ofNat 64 (16 * k)) 16
          (fun j => s.mem (a + BitVec.ofNat 64 (16 * k + j))) := by
        rw [hm, e0]
        refine (written_word v.mem _ 16 (v.mem.readW (v.gpr .x1) 128)).congr fun j hj => ?_
        rw [e1]
        simp only [Mem.readW, BitVec.setWidth_eq]
        rw [Mem.extractLsb'_read _ _ hj, ptr_add]
        exact hf.bytes (R := ⟨a, 16 * n⟩)
          (by simpa only [List.mem_singleton, forall_eq] using hsep)
          (by change 16 * n ≤ 2 ^ 64; omega) (by change 16 * k + j < 16 * n; omega)
      obtain ⟨hf', hb'⟩ := Written.step hf hb hw (by omega) (by omega)
      refine ⟨⟨?_, ?_, ?_, (kv.trans kt).mono (by simp), hf', ?_⟩, ?_⟩
      · rw [t0, e0, show 16#64 = BitVec.ofNat 64 16 by rfl, ptr_add, Nat.mul_succ]
      · rw [t1, e1, show 16#64 = BitVec.ofNat 64 16 by rfl, ptr_add, Nat.mul_succ]
      · rw [t2, e2, Sign.ofNat_sub_one hk]
      · simpa only [Nat.mul_succ] using hb'
      · rw [t2, e2, Sign.ofNat_sub_one hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
  · exact ⟨by simpa only [Nat.mul_zero, VG.Proof.MlKem.AArch64.ptr_zero] using h1,
      by simpa only [Nat.mul_zero, VG.Proof.MlKem.AArch64.ptr_zero] using h2,
      h3, ku.keep, by rw [ku.mem]; exact Frame.refl _ _, by intro j hj; omega⟩
  · refine ⟨?_, hf, kt⟩
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => hb i (List.mem_range.mp hi)

/-- The layout check records the vector granularity as well as disjointness. -/
def copyChk (rbs wbs : List (Reg × Nat)) (dst src : Ptr) (bytes : Nat) : Bool :=
  inB wbs dst bytes && inB (rbs ++ wbs) src bytes &&
    sepB rbs wbs src bytes dst bytes && decide (0 < bytes) &&
    decide (bytes < 2 ^ 32) && decide (bytes % 16 = 0)

theorem copy_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {dst src : Ptr} {bytes : Nat}
    (hc : copyChk rbs wbs dst src bytes = true) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy dst src bytes) s fun t =>
      PPostB S s t [(dst, bytes)] ∧ t.gpr .x24 = s.gpr .x24 ∧
      bytesAt t.mem (pa s dst) bytes = bytesAt s.mem (pa s src) bytes := by
  simp only [copyChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hw, hr⟩, hd⟩, h0⟩, hn⟩, halign⟩ := hc
  have he : 16 * (bytes / 16) = bytes := by omega
  have hi := (sepB_spec hd).2.1
  have h := copy_core (n := bytes / 16) (by omega) (by omega)
    (L.ptrBs hi) (L.ptrBs hr) s
  rw [he] at h
  exact WP.mono (h (L.inR hr) (L.inW hw) (L.disj hd))
    fun t ⟨hb, hf, hk⟩ => ⟨postB_of_keep hk (by decide) hf, hk.get .x24, hb⟩

abbrev copyHint (bytes : Nat) : VG.Taint.Hint AArch64.Taint.T :=
  if bytes = 0 then .block [] else
    .seq (AArch64.Taint.ofRegs [.x0, .x1, .x2]) (.block [])
      (.loop (AArch64.Taint.ofRegs [.x0, .x1, .x2]) (.block []))

theorem copy_taint {dst src : Reg} (hd : dst = .x26 ∨ dst = .x28)
    (hs : src = .x21 ∨ src = .x25) (od os bytes : Nat) :
    (taint.check (AArch64.Taint.ofRegs [.x21, .x25, .x26, .x28])
      (Impl.MlDsa.AArch64.PreparedKey.copy (dst, od) (src, os) bytes)
      (copyHint bytes)).isSome = true := by
  rcases hd with rfl | rfl <;> rcases hs with rfl | rfl <;>
    dsimp only [Impl.MlDsa.AArch64.PreparedKey.copy, copyHint,
      Impl.MlDsa.AArch64.Call.lea, Impl.MlDsa.AArch64.Call.movV] <;>
    (repeat' split) <;> rfl

end VG.Proof.MlDsa.AArch64.PreparedKey
