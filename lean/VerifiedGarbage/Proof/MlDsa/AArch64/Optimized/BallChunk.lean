import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallTry

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (IPoly q n)
open VG.Proof.MlDsa.AArch64.Sample.Ball (CStored)
open VG.Impl.MlDsa.AArch64.Optimized.Ball (earlyBody)

/-- The parser's scalar state; independent of buffer placement and budget. -/
structure Parser (a : Addr) (c : IPoly) (i : Nat) (w : BitVec 64) (s : State) : Prop where
  x26 : s.gpr .x26 = a
  x9 : s.gpr .x9 = w
  x10 : (s.gpr .x10).toNat = i
  x11 : (s.gpr .x11).toNat = 256-i
  x12 : (s.gpr .x12).toNat = q-2
  x15 : (s.gpr .x15).toNat = 1
  stored : CStored s.mem a c

abbrev chunkRegs : List Reg := [.x2,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x13,.x14]

/-- One consumed byte, with the remaining-byte counter zeroed on completion. -/
theorem body_ok {τ i b : Nat} {signs : Array Bool} {a : Addr} {c : IPoly} {j : Byte}
    {s : State} (hi : i<256) (hb0 : 0<b) (hb64 : b<2^64)
    (hp : Parser a c i (s.gpr .x9) s)
    (hsign : (s.gpr .x9).getLsbD 0 = signs.getD (i+τ-256) false)
    (h5 : (s.gpr .x5).toNat=b)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x2) 1) (hj : s.mem (s.gpr .x2)=j)
    (hw : ∀ k<256, InRegions s.wr (coeffAddr a k) 4) :
    WP isa earlyBody s fun u =>
      Keep chunkRegs s u ∧ Frame [polyR a] s.mem u.mem ∧
      u.gpr .x2=s.gpr .x2+1 ∧
      (u.gpr .x5).toNat=(if (bStep τ signs (c,i) j).2=256 then 0 else b-1) ∧
      Parser a (bStep τ signs (c,i) j).1 (bStep τ signs (c,i) j).2
        (s.gpr .x9 >>> ((bStep τ signs (c,i) j).2-i)) u := by
  refine WP.seq (WP.mono (try_ok hi hp.x26 hsign hp.x10 hp.x11 hp.x12 hp.x15 hin hj hw hp.stored)
    fun t ht => ?_)
  refine WP.seq (wp_addImm (by decide) fun t₁ h₁ e₁ =>
    wp_subImm (by decide) fun t₂ h₂ e₂ => wp_nil ?_)
  have kt := ((ht.keep.trans h₁.keep).trans h₂.keep).mono (rs' := chunkRegs) (by decide)
  have mt : t₂.mem=t.mem := by rw [h₂.mem,h₁.mem]
  have x2 : t₂.gpr .x2=s.gpr .x2+1 := by rw [h₂.get .x2,e₁,ht.keep.get .x2]; rfl
  have x5 : (t₂.gpr .x5).toNat=b-1 := by
    rw [e₂,toNat_sub_n (by rw [h₁.get .x5,ht.keep.get .x5,h5]; simp; omega),
      h₁.get .x5,ht.keep.get .x5,h5]; rfl
  have pp : Parser a (bStep τ signs (c,i) j).1 (bStep τ signs (c,i) j).2
      (s.gpr .x9 >>> ((bStep τ signs (c,i) j).2-i)) t₂ :=
    ⟨by rw [kt.get .x26,hp.x26], by rw [h₂.get .x9,h₁.get .x9,ht.x9],
      by rw [h₂.get .x10,h₁.get .x10,ht.x10],by rw [h₂.get .x11,h₁.get .x11,ht.x11],
      by rw [kt.get .x12,hp.x12],by rw [kt.get .x15,hp.x15],by rw [mt]; exact ht.stored⟩
  have hle : (bStep τ signs (c,i) j).2≤256 := bStep_le (by exact Nat.le_of_lt hi) j
  by_cases done : (bStep τ signs (c,i) j).2=256
  · refine WP.ite true (by rw [eval_zero,eq_zero_iff,pp.x11,done]; rfl)
      (fun _ => wp_movz fun u hu eu => wp_nil ?_) (fun h => nomatch h)
    refine ⟨(kt.trans hu.keep).mono (by decide), ?_, ?_, ?_, ?_⟩
    · rw [hu.mem,mt]; exact ht.frame
    · rw [hu.get .x2,x2]
    · rw [eu,ifT done]; rfl
    · exact ⟨by rw [hu.get .x26,pp.x26],by rw [hu.get .x9,pp.x9],
        by rw [hu.get .x10,pp.x10],by rw [hu.get .x11,pp.x11],
        by rw [hu.get .x12,pp.x12],by rw [hu.get .x15,pp.x15],by rw [hu.mem]; exact pp.stored⟩
  · refine WP.ite false (by rw [eval_zero,eq_zero_iff,pp.x11]; simp; omega)
      (fun h => nomatch h) (fun _ => wp_nil ?_)
    exact ⟨kt,by rw [mt]; exact ht.frame,x2,by rw [ifF done]; exact x5,pp⟩
end VG.Proof.MlDsa.AArch64.Optimized.Ball
