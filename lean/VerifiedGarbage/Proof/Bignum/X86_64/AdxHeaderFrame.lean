import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave

/-! ## AdxHeaderRestore -/
section

namespace VG.Proof.Bignum.X86_64.AdxHeader
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.MlKem.X86_64 (Keep)

theorem clearHigh_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hp : s.gpr .r9 = off B e) (he : e+16 ≤ Z) :
    WP isa (.block AdxHeader.clearHigh) s fun t =>
      (∀ q < 2, word t.mem B (e+8*q) = 0) ∧ Outside B e 16 s.mem t.mem ∧ Keep [.rax] s t := by
  have nowrap := hs.nowrap
  unfold AdxHeader.clearHigh
  rw [show ([.mov32 .rax (.imm 0),.store (at_ .r9 0) .rax,.store (at_ .r9 8) .rax] : List Instr) =
    [.mov32 .rax (.imm 0)] ++ ([.store (at_ .r9 0) .rax] ++ [.store (at_ .r9 8) .rax]) from rfl,
    WP.block_append_iff]
  refine WP.mono (movZero_ok s .rax) fun a ⟨za,_,_,ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeAt_ok (hs.congr ka.2.2.2) ((ka.gpr (by decide)).trans hp) (by omega : e+0+8 ≤ Z))
    fun b ⟨vb,ob,kb⟩ => ?_
  have kab := ka.keep.trans kb
  refine WP.mono (storeAt_ok (hs.congr kab.2.2) ((kab.gpr (by decide)).trans hp) he)
    fun t ⟨vt,ot,kt⟩ => ?_
  simp only [Nat.add_zero] at vb ob
  rw [za] at vb
  rw [kb.gpr (r := .rax) (by simp),za] at vt
  rw [ka.2.1] at ob
  refine ⟨?_,(ob.mono (o' := e) (n' := 16) (by omega) (by omega)).trans
    (ot.mono (o' := e) (n' := 16) (by omega) (by omega)),(kab.trans kt).mono (by simp)⟩
  intro q hq
  rcases (show q=0 ∨ q=1 by omega) with rfl | rfl
  · simp only [Nat.mul_zero,Nat.add_zero]
    rw [ot.word (by omega) (by omega)]; exact vb
  · simpa only [Nat.mul_one] using vt

theorem restore_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi) (hZ : slot w 8 ≤ Z) :
    WP isa AdxHeader.restore s fun t =>
      (∀ q < 2, word t.mem B (8*sFn 12+8*q) = word s.mem B (slot w aAcc+8*q)) ∧
      (∀ q < 2, word t.mem B (8*sFn 14+8*q) = word s.mem B (highPad w+8*q)) ∧
      (∀ q < 2, word t.mem B (highPad w+8*q) = 0) ∧
      Frm B [(8*sFn 12,32),(highPad w,16)] s.mem t.mem ∧ Keep [.rax,.r8,.r9] s t := by
  have nowrap := hs.nowrap
  have pads := pads_bound hZ
  have head : hdrBytes ≤ slot w aAcc := by unfold slot; omega
  unfold AdxHeader.restore
  refine WP.seq (WP.mono (bases_ok hs hd hh hZ) fun a ⟨lo,hi,ma,ka⟩ => ?_)
  have da : a.gpr .rdi = off B 0 := by
    rw [show off B 0 = B from BitVec.add_zero B]
    exact (ka.gpr (by decide)).trans hd
  refine WP.seq (WP.mono (copyPair_ok (hs.congr ka.2.2) lo da (by decide) (by decide)
    (by omega) (by unfold sFn hdrBytes at *; omega) (by unfold sFn hdrBytes at *; omega))
    fun b ⟨vb,ob,kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.seq (WP.mono (copyPair_ok (hs.congr kab.2.2) ((kb.gpr (by decide)).trans hi)
    ((kb.gpr (by decide)).trans da) (by decide) (by decide)
    (by omega) (by unfold sFn hdrBytes at *; omega) (by unfold sFn hdrBytes at *; omega))
    fun c ⟨vc,oc,kc⟩ => ?_)
  have kabc := kab.trans kc
  refine WP.mono (clearHigh_ok (hs.congr kabc.2.2) (((kb.trans kc).gpr (by simp)).trans hi) pads.2)
    fun t ⟨zt,ot,kt⟩ => ?_
  simp only [Nat.add_zero,Nat.zero_add] at vb ob vc oc
  rw [ma] at vb ob
  have ob' := ob.mono (o' := 8*sFn 12) (n' := 32) (by omega) (by omega)
  have oc' := oc.mono (o' := 8*sFn 12) (n' := 32) (by unfold sFn; omega) (by unfold sFn; omega)
  refine ⟨?_,?_,zt,((Frm.of_outside ob' (by simp)).trans (Frm.of_outside oc' (by simp))).trans
    (Frm.of_outside ot (by simp)),(kabc.trans kt).mono (by simp)⟩
  · intro q hq
    rw [ot.word (by unfold sFn hdrBytes at *; omega) (by unfold sFn; omega),
      oc.word (by unfold sFn; omega) (by unfold sFn; omega)]
    exact vb q hq
  · intro q hq
    rw [ot.word (by unfold sFn hdrBytes at *; omega) (by unfold sFn; omega),vc q hq,
      ob.word (by unfold sFn hdrBytes at *; omega) (by omega)]

end VG.Proof.Bignum.X86_64.AdxHeader

end

/-! ## AdxHeaderFrame -/
section

/-! Restoring the borrowed words removes the header from the final write frame. -/
namespace VG.Proof.Bignum.X86_64.AdxHeader
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem byte_of_word_eq {m m' : Mem} {B x : Addr} {d : Nat}
    (h : word m' B d = word m B d) (lo : d ≤ ofs B x) (hi : ofs B x < d+8) : m' x = m x := by
  let k := ofs B x-d
  have hk : k < 8 := by omega
  have addr : off B d+BitVec.ofNat 64 k = x := by
    change off (off B d) k = x
    rw [off_off,show d+k=ofs B x by omega]
    simp only [off,ofs,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    rw [BitVec.add_comm,BitVec.sub_add_cancel]
  have hv := congrArg (fun v : BitVec 64 => v.extractLsb' (8*k) 8) h
  change (m'.read (off B d) 8).extractLsb' (8*k) 8 = (m.read (off B d) 8).extractLsb' (8*k) 8 at hv
  rw [Mem.extractLsb'_read _ _ hk,Mem.extractLsb'_read _ _ hk,addr] at hv
  exact hv

theorem bytes_of_header_words {m m' : Mem} {B x : Addr} {H : Nat}
    (h : ∀ q < 4, word m' B (H+8*q) = word m B (H+8*q))
    (lo : H ≤ ofs B x) (hi : ofs B x < H+32) : m' x = m x := by
  let q := (ofs B x-H)/8
  have hq : q < 4 := by omega
  exact byte_of_word_eq (h q hq) (by omega) (by omega)

/-- Save, a body restricted to its product and borrowed header, and restore
change only the two Montgomery scratch arrays. -/
theorem restored_frame {m₀ m₁ m₂ m₃ : Mem} {B : Addr} {w : Nat}
    (hZ : highPad w+16 ≤ 2^64)
    (saveLo : ∀ q < 2, word m₁ B (slot w aAcc+8*q) = word m₀ B (8*sFn 12+8*q))
    (saveHi : ∀ q < 2, word m₁ B (highPad w+8*q) = word m₀ B (8*sFn 14+8*q))
    (saveFrame : Frm B [(slot w aAcc,16),(highPad w,16)] m₀ m₁)
    (bodyFrame : Frm B [(slot w aAcc+16,16*w),(8*sFn 12,32)] m₁ m₂)
    (restoreLo : ∀ q < 2, word m₃ B (8*sFn 12+8*q) = word m₂ B (slot w aAcc+8*q))
    (restoreHi : ∀ q < 2, word m₃ B (8*sFn 14+8*q) = word m₂ B (highPad w+8*q))
    (restoreFrame : Frm B [(8*sFn 12,32),(highPad w,16)] m₂ m₃) :
    Outside B (slot w aAcc) (16*w+32) m₀ m₃ := by
  have header : ∀ q < 4, word m₃ B (8*sFn 12+8*q) = word m₀ B (8*sFn 12+8*q) := by
    intro q hq
    by_cases low : q < 2
    · rw [restoreLo q low,bodyFrame.word_eq (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> simp only [] <;>
          simp only [slot,aAcc,hdrBytes,sFn] <;> omega) (by unfold highPad at hZ; omega)]
      exact saveLo q low
    · have qh : q-2 < 2 := by omega
      have eq : 8*sFn 12+8*q = 8*sFn 14+8*(q-2) := by unfold sFn; omega
      rw [eq,restoreHi (q-2) qh,bodyFrame.word_eq (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> simp only [] <;>
          simp only [highPad,slot,aAcc,hdrBytes,sFn] <;> omega) (by omega)]
      exact saveHi (q-2) qh
  intro x hx
  by_cases inside : 8*sFn 12 ≤ ofs B x ∧ ofs B x < 8*sFn 12+32
  · exact bytes_of_header_words header inside.1 inside.2
  · have outH : ofs B x < 8*sFn 12 ∨ 8*sFn 12+32 ≤ ofs B x := by omega
    have r3 : m₃ x = m₂ x := restoreFrame x (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> unfold highPad at * <;> omega)
    have r2 : m₂ x = m₁ x := bodyFrame x (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> omega)
    have r1 : m₁ x = m₀ x := saveFrame x (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> unfold highPad at * <;> omega)
    exact (r3.trans r2).trans r1

end VG.Proof.Bignum.X86_64.AdxHeader

end
