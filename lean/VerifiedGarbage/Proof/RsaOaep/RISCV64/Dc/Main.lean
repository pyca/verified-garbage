module

import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Unmask
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Scan
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Buf
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Shift
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Out
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Written
public import VerifiedGarbage.Proof.RsaOaep.Decode
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Mgf
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSAES-OAEP decryption on RISC-V: the decoding

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Main.lean`): `decMain_ok`, from the private
operation's outcome (`AfterPriv`), the decoding writes what `decOut`
(`Proof/RsaOaep/Decode.lean`) says to `out` and `*msg_len`, and returns its
code, as `writtenDecrypt` takes them.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes)
open VG.Proof.RsaOaep.RISCV64 (Base Saves view off off_off bytes_entry bytesAt_view)
open VG.Proof.RsaOaep (mixV srcB mk scanS accG zM decOut decode_eq scanS_inv accG_eq_zero or_eq_zero mk_eq_zero
  scan_found scan_fail scan_idx out_list out_zero lk bad srcB_eq scanS_congr map_range_getD')
open VG.Proof.RsaPss.RISCV64 (shV shV_eq)
open VG.Proof.Mgf1 (ifp ifn)

/-- The label, from the entry state. -/
abbrev labB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < xs.length) (hl : xs.length < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) = xs.getD i 0 := by
  simp only [writeBytes, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
  rw [ifp hi]

section
variable {s : State} (P : PreD s)
include P

theorem labB_eq {m : Mem} (hm : Frame [kD s, scR s] s.mem m) :
    Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat = labB s :=
  bytes_entry hm P.kl P.ls.symm (by have := (stackArg s 10).isLt; omega)

/-- The decoding, after the private operation's outcome. -/
theorem decMain_ok {H G : Hash} (hH : HashOK H) (hG : HashOK G) (hHF : H.F ≤ 208) (hGF : G.F ≤ 208)
    {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) {v : State} (A : AfterPriv s v) (hk : 2 * H.D + 2 ≤ kk s) :
    WP isa (decMain H G) v fun u => Saves s u ∧ u.rd = s.rd ∧
      Spec.RsaOaep.writtenDecrypt u.mem (s.gpr .a0) (s.gpr .a2) (kk s) ((u.gpr .a0).setWidth 32)
        (decOut Hs Gs (labB s) (privO s)) := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have hrc := rcOf_le (privO s)
  obtain ⟨hE, hSt, hDg, hB, hRs⟩ := offs'
  generalize hD : H.D = D at *
  generalize hO : privO s = o at *
  generalize hRC : rcOf o = rc at *
  have b0 := A.base
  rw [hO, hRC] at b0
  unfold decMain
  -- `EM` unmasked.
  refine unmask_ok P hG hGF hGh hGl hGv hD hD0 (by omega) (by omega) b0 fun t₁ b₁ v₁ => ?_
  -- The label's hash.
  refine WP.seq (WP.mono (hashLabel_ok P hH hHF A.mem b₁) fun t₂ ⟨b₂, _, s₂, h₂⟩ => ?_)
  -- `lHash'` against `lHash`.
  refine WP.seq (WP.mono (accLh_ok P hD hD0 (by omega) (by omega) b₂) fun t₃ ⟨b₃, m₃, g₃, a₃⟩ => ?_)
  -- The scan.
  refine WP.seq (WP.mono (scan_ok P hD (by omega) (by omega) b₃) fun t₄ ⟨b₄, m₄, g₄, a₄, i₄⟩ => ?_)
  -- The buffer.
  refine WP.seq (WP.mono (clearBuf_ok P b₄) fun t₅ ⟨b₅, g₅, v₅⟩ => ?_)
  refine WP.seq (WP.mono (copyT_ok P hD (by omega) (by omega) b₅) fun t₆ ⟨b₆, g₆, v₆⟩ => ?_)
  generalize hsc : scanS (fun i => view t₃.mem (Sd s) (1 + 2 * D + i)) (t₃.gpr .s5) (kk s - (2 * D + 1)) = sc
    at a₄ i₄
  obtain ⟨idx, hidx, hidx'⟩ := scan_idx (fun i => view t₃.mem (Sd s) (1 + 2 * D + i)) (t₃.gpr .s5)
    (kk s - (2 * D + 1))
  rw [hsc] at hidx
  have h6 : t₆.gpr .s6 = BitVec.ofNat 64 idx := by
    rw [g₆.get .s6, g₅.get .s6, i₄, hidx]
  refine WP.seq (WP.mono (shift_ok P b₆ h6 (by omega)) fun t₇ ⟨b₇, k₇, v₇⟩ => ?_)
  -- `ok`, `out`, the length and the result.
  refine WP.seq (WP.mono (okMask_ok P b₇ (by omega)) fun t₈ ⟨b₈, m₈, g₈, o₈⟩ => ?_)
  refine WP.seq (WP.mono (outLoop_ok P b₈) fun t₉ ⟨sv₉, rd₉, g₉, m₉⟩ => ?_)
  refine WP.mono (decRet_ok P hD (by omega) (rc := rc) (idx := idx) sv₉
    (by rw [g₉.get .s1, g₈.get .s1, Base.dk b₇]) (by rw [g₉.get .s3, g₈.get .s3, Base.dml b₇])
    (by rw [g₉.get .s4, g₈.get .s4, Base.drc b₇]) (by omega)
    (by rw [g₉.get .s6, g₈.get .s6, k₇.get .s6, h6])) fun u ⟨svu, rdu, mu, ru⟩ =>
    ⟨svu, rdu.trans rd₉, ?_⟩
  -- The views.
  have hS : ∀ {x}, x < oSt → ∀ p ∈ [(oSt, H.S), (oDig, H.D)], x < p.1 ∨ p.1 + p.2 ≤ x :=
    fun hx p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact .inl (by simp only; omega)
  have e2 : ∀ x < oSt, view t₂.mem (Sd s) x = view t₁.mem (Sd s) x := fun x hx => s₂ x (by omega) (hS hx)
  have hlab : Spec.Rsa.bytesAt v.mem (stackArg s 9) (stackArg s 10).toNat = labB s := labB_eq P A.mem
  rw [hlab] at h₂
  have hlh : ∀ i < D, view t₂.mem (Sd s) (oDig + i) = (Hs.hash (labB s)).getD i 0 := fun i hi => by
    have := congrArg (fun l => l.getD i 0) h₂
    rw [bytesAt_view, srcB, map_range_getD' _ (by omega)] at this
    rw [this, hHh]
  -- `lHash'`, `lHash` and the scan, on the view after unmasking.
  have hc0 : t₃.gpr .s5 = accG (view t₁.mem (Sd s) 0) (fun i => view t₁.mem (Sd s) (1 + D + i))
      (fun i => view t₂.mem (Sd s) (oDig + i)) D := by
    rw [a₃, e2 0 (by omega)]
    exact accG_congr _ D (fun i hi => e2 _ (by omega)) (fun _ _ => rfl)
  have hsc' : sc = scanS (fun i => view t₁.mem (Sd s) (1 + 2 * D + i)) (accG (view t₁.mem (Sd s) 0)
      (fun i => view t₁.mem (Sd s) (1 + D + i)) (fun i => view t₂.mem (Sd s) (oDig + i)) D) (kk s - (2 * D + 1)) := by
    rw [← hsc, hc0, m₃]
    exact scanS_congr _ _ fun i hi => e2 _ (by omega)
  rw [hsc'] at hidx
  have r5 : t₇.gpr .s5 = sc.2.2 ||| sc.1 := by
    rw [k₇.get .s5, g₆.get .s5, g₅.get .s5, a₄]
  have hok : t₉.gpr .s7 = mk (rcOf o = 1 ∧ (sc.2.2 ||| sc.1) = 0) := by
    rw [g₉.get .s7, o₈, r5, ← hRC]
  rw [hsc'] at hok
  -- The buffer.
  have hT : ∀ y < 2048, view t₆.mem (Sd s) (oBuf + y) =
      (srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD y 0 := by
    intro y hy
    rw [v₆ _ (by omega)]
    by_cases hyt : y < kk s - (2 * D + 1)
    · rw [ifp ⟨by omega, by omega⟩, show oBuf + y - oBuf = y by omega, v₅ _ (by omega), ifn (by omega), m₄, m₃,
        e2 _ (by omega), srcB, map_range_getD' _ hyt]
    · rw [ifn (by omega), v₅ _ (by omega), ifp ⟨by omega, by omega⟩]
      simp [srcB, List.getD_eq_getElem?_getD, hyt]
  have hbuf : ∀ i < kk s, view t₇.mem (Sd s) (oBuf + i) =
      (srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD (i + (idx + 1)) 0 := by
    intro i hi
    rw [v₇ _ (by omega), shV_eq _ (by omega) (fun x h₁ h₂ => by
      rw [hT x (by omega)]; simp [srcB, List.getD_eq_getElem?_getD, show ¬ x < kk s - (2 * D + 1) by omega]) hi]
    by_cases hl : i + (idx + 1) < kk s
    · rw [ifp hl, hT _ (by omega)]
    · rw [ifn hl]; simp [srcB, List.getD_eq_getElem?_getD, show ¬ i + (idx + 1) < kk s - (2 * D + 1) by omega]
  -- `out`, `*msg_len` and the result.
  have hu : ∀ x, ¬ (mlR s).Contains x 1 → u.mem x = t₉.mem x := fun x hx => by
    rw [mu]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self (mlR s)) _ (Region.contains_self _ _)) x
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hx)
  have hlen : ((Spec.Rsa.bytesAt t₈.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t₈.gpr .s7)).length =
      kk s := by simp [bytesAt_length]
  have hout : ∀ i < kk s, u.mem (s.gpr .a0 + BitVec.ofNat 64 i) =
      andB ((srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD (i + (idx + 1)) 0) (t₉.gpr .s7) := by
    intro i hi
    rw [hu _ (fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega) (by omega)) hc), m₉]
    rw [writeBytes_at _ _ _ (by rw [hlen]; exact hi) (by rw [hlen]; omega), List.getD_eq_getElem?_getD,
      List.getElem?_map, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some, Option.getD_some]
    rw [g₉.get .s7]
    congr 1
    rw [m₈, ← hbuf i hi]; show t₇.mem (off (off (Sd s) oBuf) i) = _; rw [off_off]; rfl
  have hml : u.mem.readW (s.gpr .a2) 64 = (BitVec.ofNat 64 (kk s) - BitVec.ofNat 64 (2 * D + 2) -
      BitVec.ofNat 64 idx) &&& t₉.gpr .s7 := by
    rw [mu, Mem.readW_writeW_self64, show s.gpr .a4 = BitVec.ofNat 64 (kk s) from
      (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm]
  rw [hok] at hout hml ru
  exact dec_written hGv hHv hHl (by omega) hk2 v₁ hlh (fun em he => by
      have := A.em; rw [hO, he] at this; exact this.symm)
    hidx (by rcases hidx' with h | h; exact .inl h; exact .inr h) hout hml (by rw [ru, hRC])

end

end VG.Proof.RsaOaep.RISCV64.Dec
