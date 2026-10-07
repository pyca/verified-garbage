import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderRestore

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
