module

-- separate module: it builds in parallel with the constant-time proofs (`CTBase` to `CTLabel`), which
-- `Verified` also needs.

import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Out
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Mgf
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Unmask
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Scan
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Buf
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Shift
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Written
public import VerifiedGarbage.Proof.RsaOaep.Decode
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP decryption on RISC-V: correctness

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Correct.lean`): the entry, the private
operation (`priv_ok`), the check of `k ≥ 2 hLen + 2` (public), then either
zeros and the result `r = 2 ? 2 : 0` (`decFail_ok`, which is what `decOut`
says for a too short `k`) or the decoding (`decMain_ok`), and the restores:
RSAES-OAEP-DECRYPT (RFC 8017 §7.1.2). `code_correct`: the function against
its shared contract.
-/

@[expose] public section

/-!
## RSAES-OAEP decryption on RISC-V: the decoding

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Main.lean`): `decMain_ok`, from the private
operation's outcome (`AfterPriv`), the decoding writes what `decOut`
(`Proof/RsaOaep/Decode.lean`) says to `out` and `*msg_len`, and returns its
code, as `writtenDecrypt` takes them.
-/
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


namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_sub wp_srl wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes)
open VG.Proof.RsaOaep.RISCV64 (Saves restore_ok ne_zero_ltBit)
open VG.Proof.RsaOaep (decOut decOut_short)
open VG.Proof.Mgf1 (ifp ifn)

/-- The result and the outputs, from the entry state `s`. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ Spec.RsaOaep.writtenDecrypt s'.mem (s.gpr .a0) (s.gpr .a2) (kk s) ((s'.gpr .a0).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ Spec.RsaOaep.writtenDecrypt t.mem (s.gpr .a0) (s.gpr .a2) (kk s) ((t.gpr .a0).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

theorem AfterPriv.only {s v v' : State} {rs : List Reg} (A : AfterPriv s v) (P : PreD s) (o : Only rs v v')
    (hrs : ∀ r ∈ rs, r ∉ Proof.RsaOaep.RISCV64.fixed := by decide) : AfterPriv s v' := by
  have hm : v'.mem = v.mem := o.mem
  have b := A.base
  rw [← hm] at b
  exact ⟨b.only (fits P rfl rfl) o hrs, hm ▸ A.mem, hm ▸ A.em⟩

/-- `EM` too short for the hash: what decryption returns, from the private
operation's result. -/
theorem decOut_short' {Hs Gs : Spec.Mgf1.Hash} {lab : List Byte} {o : Spec.Rsa.Outcome} {k : Nat}
    (hl : ∀ em, o = .ok em → em.length = k) (hk : k < 2 * Hs.len + 2) :
    decOut Hs Gs lab o = if rcOf o = 2 then .fault else .invalid := by
  rw [decOut_short hl hk]
  cases o <;> rfl

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) (fH : H.F ≤ 208) (fG : G.F ≤ 208)
  {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
  {s : State} (P : PreD s)
include hH hG fH fG hHh hHl hHv hGh hGl hGv P

omit hH hG fH fG hHh hHv hGh hGl hGv in
theorem fail_done {v : State} (A : AfterPriv s v) (hk : kk s < 2 * H.D + 2) :
    WP isa decFail v (Done Hs Gs s) := by
  have hrc := rcOf_le (privO s)
  refine WP.mono (decFail_ok P A.base hrc) fun u ⟨sv, _, hm, h3⟩ => ⟨sv, ?_⟩
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have hl : ∀ em, privO s = .ok em → em.length = kk s := fun em he => by
    have := A.em; rw [he] at this; simp only [emOf] at this; rw [← this, bytesAt_length]
  rw [decOut_short' hl (by rw [hHl]; exact hk)]
  have hout : Spec.Rsa.bytesAt u.mem (s.gpr .a0) (kk s) = List.replicate (kk s) 0 := by
    have e := bytesAt_writeBytes v.mem (s.gpr .a0) (List.replicate (kk s) 0)
      (by rw [List.length_replicate]; omega)
    rw [List.length_replicate] at e
    rw [← e, hm]
    have f : Frame [mlR s] (writeBytes v.mem (s.gpr .a0) (List.replicate (kk s) 0))
        ((writeBytes v.mem (s.gpr .a0) (List.replicate (kk s) 0)).writeW (s.gpr .a2) (0#64)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact f _ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega) (by omega)) hc)
  have hml : u.mem.readW (s.gpr .a2) 64 = 0 := by rw [hm, Mem.readW_writeW_self64]; rfl
  by_cases h2 : rcOf (privO s) = 2
  · rw [ifp h2]; exact ⟨by rw [h3, ifp h2]; decide, hout, hml⟩
  · rw [ifn h2]; exact ⟨by rw [h3, ifn h2]; decide, hout, hml⟩

omit hH hG fH fG hHh hHl hHv hGh hGl hGv in
/-- The check of `k`: in `a0`, whether it is too short. -/
theorem chk_ok (hD64 : H.D ≤ 64) {v : State} (A : AfterPriv s v) :
    WP isa (.block (chkK H)) v fun v' => AfterPriv s v' ∧ (v'.gpr .a0 != 0) = decide (kk s < 2 * H.D + 2) := by
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  refine wp_li (imm := 2 * H.D + 2) (by omega) fun v₁ o₁ e₁ => wp_sub fun v₂ o₂ e₂ => wp_srl fun v₃ o₃ e₃ =>
    wp_nil ?_
  have k₃ : Only [.a0] v v₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨A.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, o₁.get .s1, Base.dk A.base, show s.gpr .a4 = BitVec.ofNat 64 (s.gpr .a4).toNat by simp]
  exact ne_zero_ltBit (by omega) (by omega)

/-- The branch on the check of `k`. -/
theorem ite_done {v : State} (A : AfterPriv s v) (r0 : (v.gpr .a0 != 0) = decide (kk s < 2 * H.D + 2)) :
    WP isa (.ite (.nonzero .a0) decFail (decMain H G)) v (Done Hs Gs s) :=
  WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P A (by rw [r0] at hc; simpa using hc))
    (fun hc => WP.mono (decMain_ok P hH hG fH fG hHh hHl hHv hGh hGl hGv A
      (by rw [r0] at hc; simp at hc; omega)) fun u ⟨sv, _, hw⟩ => ⟨sv, hw⟩)

theorem checks_done {v : State} (A : AfterPriv s v) :
    WP isa (.block (chkK H)) v fun v' =>
      WP isa (.ite (.nonzero .a0) decFail (decMain H G)) v' (Done Hs Gs s) :=
  WP.mono (chk_ok P hH.hD64 A) fun _ ⟨A', r0⟩ => ite_done hH hG fH fG hHh hHl hHv hGh hGl hGv P A' r0

theorem code_ok : WP isa (decrypt H G) s (Post Hs Gs s) := by
  refine WP.alloc (by decide) (by have := P.sp1; rw [stackBytes_eq] at this; unfold frameBytes; omega) ?_
  refine WP.seq (WP.mono (entry_ok P) fun t E => ?_)
  refine WP.seq (WP.mono (priv_ok P E) fun v A => ?_)
  refine WP.seq (WP.mono (checks_done hH hG fH fG hHh hHl hHv hGh hGl hGv P A) fun v' h => WP.seq (WP.mono h
    fun t' ⟨sv, res⟩ => WP.mono (restore_ok sv (fb_al8 P)) fun w ⟨habi, h3, hm⟩ => ⟨habi, ?_⟩))
  show Spec.RsaOaep.writtenDecrypt w.mem _ _ _ ((w.gpr .a0).setWidth 32) _
  rw [hm, h3]
  exact res

end

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) (fH : H.F ≤ 208) (fG : G.F ≤ 208)
  {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
include hH hG fH fG hHh hHl hHv hGh hGl hGv

/-- The correctness of `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`, against its shared
contract. -/
theorem code_correct (s : State) (h : (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pre s) :
    ∃ t s', Exec isa (decrypt H G) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).post s s' := by
  have P : PreD s := preD_of h
  obtain ⟨t, s', he, habi, hr⟩ := code_ok hH hG fH fG hHh hHl hHv hGh hGl hGv P
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes = 3471 + 1 := rfl
  rw [e]
  sig_post [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, stackArgs_fifteen, List.append_eq]
  rw [Proof.RsaOaep.decrypt_eq (by rw [bytesAt_length, bytesAt_length])]
  exact hr

end

end VG.Proof.RsaOaep.RISCV64.Dec
