module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptPadding
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncodeTiming

/-! # Relating encodings with independent secret messages and padding strings -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Encrypt

structure EncodeReady (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  context : Context g bs s
  dst : s.gpr .edi = g.temporary
  src : s.gpr .esi = g.sources 3
  count : s.gpr .ebp = BitVec.ofNat 32 g.paddingLength

theorem encoding_relCT {g : Geometry} {bs1 bs2 : Fin 5 → List Byte} :
    RelCT isa (fun s t => EncodeReady g bs1 s ∧ EncodeReady g bs2 t) encoding (fun _ _ => True) := by
  unfold encoding
  apply RelCT.assoc
  intro s t tr ur sf tf H E F
  obtain ⟨hs, ht⟩ := H
  have len : (bs1 3).length = (bs2 3).length :=
    (hs.context.sources 3).length.trans (ht.context.sources 3).length.symm
  have room (bs : Fin 5 → List Byte) (s : State) (h : Context g bs s) :
      ([0, 2] ++ bs 3).length < g.length := by
    have pl : (bs 3).length = g.paddingLength := (h.sources 3).length
    have := h.valid.padding
    have := h.valid.messageFits
    simp only [List.length_append, List.length_cons, List.length_nil, pl]
    omega
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have agree : VG.X86.Taint.Agree copyTaint s t := agree_regs (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hs.dst.trans ht.dst.symm
        · exact hs.src.trans ht.src.symm
        · exact hs.count.trans ht.count.symm)
      have T1 := (padding_relCT _ _ _ _ _ _ agree E1 F1).1
      have ws := wp_result (padding_ok hs.context hs.dst hs.src hs.count) E1
      have wt := wp_result (padding_ok ht.context ht.dst ht.src ht.count) F1
      cases E2 with
      | seq E3 E4 =>
        cases F2 with
        | seq F3 F4 =>
          have agreeArgs : VG.X86.Taint.Agree (τr [.esp, .edi]) _ _ := agree_regs (by
            intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact (ws.rest.1 .esp (by decide)).trans
                ((hs.context.sp.trans ht.context.sp.symm).trans (wt.rest.1 .esp (by decide)).symm)
            · rw [ws.cursor, wt.cursor, hs.dst, ht.dst, List.length_append, List.length_append, len])
          have T2 := (messageArgs_relCT _ _ _ _ _ _ agreeArgs E3 F3).1
          obtain ⟨wcs, ss, cs, _⟩ := wp_result (messageArgs_ok hs.context hs.dst (room _ _ hs.context) ws) E3
          obtain ⟨wct, st, ct, _⟩ := wp_result (messageArgs_ok ht.context ht.dst (room _ _ ht.context) wt) F3
          have addresses : s.gpr .edi + BitVec.ofNat 32 ([0, 2] ++ bs1 3 ++ [0]).length =
              t.gpr .edi + BitVec.ofNat 32 ([0, 2] ++ bs2 3 ++ [0]).length := by
            rw [hs.dst, ht.dst]
            simp only [List.length_append, len]
          have cursors := wcs.cursor.trans (addresses.trans wct.cursor.symm)
          have agreeMsg : VG.X86.Taint.Agree copyTaint _ _ := agree_regs (by
            intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact cursors
            · exact ss.trans st.symm
            · exact cs.trans ct.symm)
          have T3 := (message_relCT _ _ _ _ _ _ agreeMsg E4 F4).1
          exact ⟨by rw [T1, T2, T3], trivial⟩

end VG.Proof.RsaPkcs1Enc.X86.Enc
