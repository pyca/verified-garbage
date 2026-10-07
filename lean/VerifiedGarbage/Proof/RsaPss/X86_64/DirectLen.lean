import VerifiedGarbage.Proof.RsaPss.X86_64.BufferCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk

/-! Direct, word-sized placement of a public one-block hash length field. -/
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Bignum (off)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

theorem directLen_ok {H : Hash} (hH : HashOK H) {u : State} {F S : Addr} (L : Lay u F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {len : List Byte}
    (hlen : ∀ i < H.P.L, V (oLen + i) = len.getD i 0) :
    WP isa (directLen H) u fun t => Lay t F S ∧ Keep [.rsi, .rcx, .rax, .r8] u t ∧
      Rep t.mem F S (cpV V (fun i => len.getD i 0) (oY + (H.P.B - H.P.L)) H.P.L) W := by
  have hL := hH.dims.L
  have hB := hH.B_le
  unfold directLen
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx] (Q := fun v =>
    v.gpr .rsi = off S oLen ∧ v.gpr .rcx = off S (oY + (H.P.B - H.P.L)) ∧ v.mem = u.mem)
    ?_ rfl) fun v ⟨⟨hs, hd, hm⟩, hk⟩ => ?_)
  · have hslot := L.slot
    simp only [Bignum.word] at hslot
    xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hslot,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oLen < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oY + (H.P.B - H.P.L) < 2 ^ 31 by unfold oY; omega)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have finish : ∀ t, Lay t F S → Keep [.rax, .r8] v t →
      Rep t.mem F S (cpV V (fun i => V (oLen + i)) (oY + (H.P.B - H.P.L)) H.P.L) W →
      Lay t F S ∧ Keep [.rsi, .rcx, .rax, .r8] u t ∧
      Rep t.mem F S (cpV V (fun i => len.getD i 0) (oY + (H.P.B - H.P.L)) H.P.L) W := by
    intro t Lt kt Rt
    refine ⟨Lt, (hk.trans kt).mono (by decide), ?_⟩
    refine (congrArg (fun V' => Rep t.mem F S V' W) (funext fun x => ?_)).mp Rt
    simp only [cpV]
    split
    · exact hlen _ (by omega)
    · rfl
  split
  · rename_i h8
    have hwords : 8 * (H.P.L / 8) = H.P.L := by omega
    refine WP.mono (copyScratchWords_ok Lv (hm ▸ R) (by decide) (by decide)
      (by rw [hwords]; unfold oLen oRsa; omega)
      (by rw [hwords]; unfold oY oRsa; omega)
      (by rw [hwords]; unfold oLen oY; omega) hs hd) fun t ⟨Lt, kt, Rt⟩ => ?_
    rw [hwords] at Rt
    exact finish t Lt (kt.mono (by decide)) Rt
  · exact WP.mono (copyScratchBytes_ok Lv (hm ▸ R) (by omega)
      (by unfold oLen oRsa; omega) (by unfold oY oRsa; omega)
      (by unfold oLen oY; omega) hs hd) fun t ⟨Lt, kt, Rt⟩ => finish t Lt kt Rt

theorem y_copied {B L : Nat} (msg len : List Byte) (hfit : msg.length + L < B)
    (hlen : len.length = L) (V : Nat → Byte)
    (hV : ∀ j < B, V (oY + j) = msg.getD j 0 ||| (if j = msg.length then 0x80 else 0)) :
    ∀ j < B, cpV V (fun i => len.getD i 0) (oY + (B - L)) L (oY + j) =
      RsaPss.padded B L msg len j := by
  intro j hj
  have hfb : 0 = RsaPss.lastBlk B L msg.length := (Nat.div_eq_of_lt hfit).symm
  rw [← y_padded msg len hfb (by omega) hlen V (by simpa using hV) j (by simpa using hj)]
  simp only [cpV, lenAt, Nat.mul_zero, Nat.add_zero]
  split
  · rename_i hx
    have hjm : msg.length < j := by omega
    have hm : msg.getD j 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have zo : ∀ x : Byte, 0 ||| x = x := fun _ => BitVec.zero_or
    rw [hV j hj, hm, ifn (by omega : j ≠ msg.length), zo, zo]
  · rfl

end VG.Proof.RsaPss.X86_64
