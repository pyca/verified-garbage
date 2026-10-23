module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Core
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! The last block never reads past the data buffer. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem zero_count {s : State} {n : Nat} (hn : n < 2^64) (hc : s.gpr .x3=BitVec.ofNat 64 n) :
    isa.eval (.zero .x .x3) s=some (decide (n=0)) := by
  change some (s.read .x .x3 == 0)=_
  simp only [State.read,BitVec.setWidth_eq,hc]
  congr 1
  by_cases h : n=0
  · rw [h]; rfl
  · rw [decide_eq_false h,beq_eq_false_iff_ne]
    intro he
    have h' := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn] at h'
    exact h h'

theorem prefetch_ok {s₀ s : State} {k : Nat} (hp : UPre s₀) (hk : k+1 ≤ N s₀)
    (h : Core s₀ k (k+1) s) :
    WP isa (.ite (.zero .x .x3) (.block []) (.block Impl.AesCbc.AArch64.Encrypt.prefetch)) s
      fun t => Core s₀ k (k+1) t ∧ VFrame [.v0] s t ∧
        (k+1 < N s₀ → t.v .v0=s₀.mem.readW (blk s₀ (k+1)) 128 ^^^ t.v .v7) := by
  have hev := zero_count (by have := hp.data_wrap; omega) h.count
  by_cases he : k+1=N s₀
  · refine WP.ite true ?_ (fun _ => WP.block_nil ⟨h,VFrame.refl _ _,fun hc => by omega⟩)
      (fun hf => by cases hf)
    rw [hev,he,Nat.sub_self]; rfl
  · refine WP.ite false ?_ (fun hf => by cases hf) (fun _ => ?_)
    · rw [hev,decide_eq_false (by omega)]
    · have ha : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 16) 16 := by
        rw [h.ptr,Offset.add_add_eq (Dp s₀) (show 16*k+16=16*(k+1) by omega),h.env.wr,hp.wr]
        exact ⟨dataR s₀,List.mem_append_right _ (by simp),
          Offset.contains_base (Dp s₀) (d:=16*(k+1)) (n:=16) (k:=16*N s₀)
            (by omega) (by have := hp.data_wrap; omega)⟩
      refine WP.mono (load_ok s 16 (by decide) ha) fun t ht => ?_
      subst ht
      have hf := loaded_frame s 16
      refine ⟨h.vframe hf (by decide),hf,?_⟩
      intro _
      change s.mem.readW (s.gpr .x2+BitVec.ofNat 64 16) 128 ^^^ s.v .v7=_
      rw [h.ptr,Offset.add_add_eq (Dp s₀) (show 16*k+16=16*(k+1) by omega),
        original_read h.data (by omega) (by omega)]
      rfl
end VG.Proof.AesCbc.AArch64.Encrypt
