module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Unmask
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Scan
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Shift
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Out
public import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Buf
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfStepsT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Tables
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-! ### `RsaOaep.PPC64LE.Dc.Main`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: the decoding

Untrusted: everything here is checked by Lean. `decMain_ok`: from the
private operation's outcome (`AfterPriv`), the decoding writes what
`decOut` (`Proof/RsaOaep/Decode.lean`) says to `out` and `*msg_len`, and
returns its code, as `writtenDecrypt` takes them.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes)
open VG.Proof.RsaOaep (mixV srcB mk scanS accG zM decOut decode_eq scanS_inv accG_eq_zero or_eq_zero mk_eq_zero
  scan_found scan_fail scan_idx out_list out_zero lk bad srcB_eq)
open VG.Proof.RsaPss.PPC64LE (shV shV_eq)
open VG.Proof.Mgf1 (ifp ifn)

/-- The label, from the entry state. -/
abbrev labB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < xs.length) (hl : xs.length < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) = xs.getD i 0 := by
  simp only [writeBytes, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hl] : i < 2 ^ 64)]
  rw [ifp hi]

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

theorem labB_eq {m : Mem} (hm : Frame [kD s, scR s] s.mem m) :
    Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat = labB s :=
  bytes_entry hm P.kl P.ls.symm (by have := (stackArg s 10).isLt; omega_using [])

/-- The decoding, after the private operation's outcome. -/
theorem decMain_ok {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
    (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
    {f : Fns} (T : TabS G f 16 (SD s) s (stackArg s 16)) (TL : TabS H f 15 (SD s) s (stackArg s 15)) {v : State}
    (A : AfterPriv s v) (hsy : v.syms = s.syms)
    (hk : 2 * H.D + 2 ≤ kk s) :
    WP isa (decMain H f) v fun u => Saves s u ∧ u.rd = s.rd ∧
      Spec.RsaOaep.writtenDecrypt u.mem (s.gpr .r3) (s.gpr .r5) (kk s) ((u.gpr .r3).setWidth 32)
        (decOut Hs Gs (labB s) (privO s)) := by
  have hD0 := hH.hD0
  have hDF := hH.hDF
  have hFD := hH.hFD64
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have hrc := rcOf_le (privO s)
  obtain ⟨hE, hSt, hDg, hW, hB, hRs⟩ := offs'
  generalize hD : H.D = D at *
  generalize hO : privO s = o at *
  generalize hRC : rcOf o = rc at *
  have b0 := A.base
  rw [hO, hRC] at b0
  unfold decMain
  -- `EM` unmasked.
  refine unmask_ok P hG (tabS_wm P T A.mem) hGh hGl hGv hD hD0 (by omega_using [hFD, hDF]) (by omega_using [hk]) b0 hsy fun t₁ b₁ y₁ v₁ => ?_
  -- The label's hash, through its table.
  refine WP.seq (WP.mono (hashLabelT_ok P hH (tabS_wmL P TL A.mem) b₁ y₁) fun t₂ ⟨⟨b₂, _, s₂, h₂⟩, _⟩ => ?_)
  -- `lHash'` against `lHash`.
  refine WP.seq (WP.mono (accLh_ok P hD hD0 (by omega_using [hFD, hDF]) (by omega_using [hk]) b₂) fun t₃ ⟨b₃, m₃, g₃, a₃⟩ => ?_)
  -- The scan.
  refine WP.seq (WP.mono (scan_ok P hD (by omega_using [hFD, hDF]) (by omega_using [hk]) b₃) fun t₄ ⟨b₄, m₄, g₄, a₄, i₄⟩ => ?_)
  -- The buffer.
  refine WP.seq (WP.mono (clearBuf_ok P b₄) fun t₅ ⟨b₅, g₅, v₅⟩ => ?_)
  refine WP.seq (WP.mono (copyT_ok P hD (by omega_using [hFD, hDF]) (by omega_using [hk]) b₅) fun t₆ ⟨b₆, g₆, v₆⟩ => ?_)
  generalize hsc : scanS (fun i => view t₃.mem (Sd s) (1 + 2 * D + i)) (t₃.gpr .r24) (kk s - (2 * D + 1)) = sc at a₄ i₄
  obtain ⟨idx, hidx, hidx'⟩ := scan_idx (fun i => view t₃.mem (Sd s) (1 + 2 * D + i)) (t₃.gpr .r24)
    (kk s - (2 * D + 1))
  rw [hsc] at hidx
  have h25 : t₆.gpr .r25 = BitVec.ofNat 64 idx := by
    rw [g₆ .r25 (by simp), g₅ .r25 (by simp), i₄, hidx]
  refine WP.seq (WP.mono (shift_ok P b₆ h25 (by omega_using [hk2, ek, hidx'])) fun t₇ ⟨b₇, k₇, v₇⟩ => ?_)
  -- `ok`, `out`, the length and the result.
  refine WP.seq (WP.mono (okMask_ok P b₇ (by omega_using [hrc])) fun t₈ ⟨b₈, m₈, g₈, o₈⟩ => ?_)
  refine WP.seq (WP.mono (outLoop_ok P b₈) fun t₉ ⟨sv₉, rd₉, g₉, m₉⟩ => ?_)
  refine WP.mono (decRet_ok P hD (by omega_using [hFD, hDF]) (rc := rc) (idx := idx) sv₉ (by rw [g₉ .r15 (by simp), g₈ .r15 (by simp), Base.r15 b₇])
    (by rw [g₉ .r17 (by simp), g₈ .r17 (by simp), Base.r17 b₇]) (by rw [g₉ .r20 (by simp), g₈ .r20 (by simp),
      Base.r20 b₇]) (by omega_using [hrc]) (by rw [g₉ .r25 (by simp), g₈ .r25 (by simp), k₇.get .r25, h25])) fun u ⟨svu, rdu, mu, ru⟩ =>
    ⟨svu, rdu.trans rd₉, ?_⟩
  -- The views.
  have hS : ∀ {x}, x < oSt → ∀ p ∈ [(oSt, H.S), (oDig, H.FD), (oW, H.W)], x < p.1 ∨ p.1 + p.2 ≤ x :=
    fun hx p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact .inl (by simp only; omega_arith)
  have e2 : ∀ x < oSt, view t₂.mem (Sd s) x = view t₁.mem (Sd s) x := fun x hx => s₂ x (by omega_using [hSt, hRs, hx]) (hS hx)
  have hlab : Spec.Rsa.bytesAt v.mem (stackArg s 9) (stackArg s 10).toNat = labB s := labB_eq P A.mem
  rw [hlab] at h₂
  have hlh : ∀ i < D, view t₂.mem (Sd s) (oDig + i) = (Hs.hash (labB s)).getD i 0 := fun i hi => by
    have := congrArg (fun l => l.getD i 0) h₂
    rw [bytesAt_view, srcB, map_range_getD' _ (by omega_using [hDF, hi])] at this
    rw [this, hHh, hH.hashTake]
    simp [List.getD_eq_getElem?_getD, show i < H.D by omega_using [hD, hi]]
  -- `lHash'`, `lHash` and the scan, on the view after unmasking.
  have hc0 : t₃.gpr .r24 = accG (view t₁.mem (Sd s) 0) (fun i => view t₁.mem (Sd s) (1 + D + i))
      (fun i => view t₂.mem (Sd s) (oDig + i)) D := by
    rw [a₃, e2 0 (by omega_using [hSt])]
    exact accG_congr _ D (fun i hi => e2 _ (by omega_using [hFD, hSt, hDF, hi])) (fun _ _ => rfl)
  have hsc' : sc = scanS (fun i => view t₁.mem (Sd s) (1 + 2 * D + i)) (accG (view t₁.mem (Sd s) 0)
      (fun i => view t₁.mem (Sd s) (1 + D + i)) (fun i => view t₂.mem (Sd s) (oDig + i)) D) (kk s - (2 * D + 1)) := by
    rw [← hsc, hc0, m₃]
    exact scanS_congr _ _ fun i hi => e2 _ (by omega_using [hk2, ek, hSt, hi])
  rw [hsc'] at hidx
  have r24 : t₇.gpr .r24 = sc.2.2 ||| sc.1 := by
    rw [k₇.get .r24, g₆ .r24 (by simp), g₅ .r24 (by simp), a₄]
  have hok : t₉.gpr .r26 = mk (rcOf o = 1 ∧ (sc.2.2 ||| sc.1) = 0) := by
    rw [g₉ .r26 (by simp), o₈, r24, ← hRC]
  rw [hsc'] at hok
  -- The buffer.
  have hT : ∀ y < 2048, view t₆.mem (Sd s) (oBuf + y) =
      (srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD y 0 := by
    intro y hy
    rw [v₆ _ (by omega_using [hB, hRs, hy])]
    by_cases hyt : y < kk s - (2 * D + 1)
    · rw [ifp ⟨by omega_using [], by omega_using [hyt]⟩, show oBuf + y - oBuf = y by omega_using [], v₅ _ (by omega_using [hFD, hRs, hDF, hy]), ifn (by omega_using [hFD, hB, hDF, hy]), m₄, m₃,
        e2 _ (by omega_using [hk2, ek, hSt, hyt]), srcB, map_range_getD' _ hyt]
    · rw [ifn (by omega_using [hyt]), v₅ _ (by omega_using [hB, hRs, hy]), ifp ⟨by omega_using [], by omega_using [hy]⟩]
      simp [srcB, List.getD_eq_getElem?_getD, hyt]
  have hbuf : ∀ i < kk s, view t₇.mem (Sd s) (oBuf + i) =
      (srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD (i + (idx + 1)) 0 := by
    intro i hi
    rw [v₇ _ (by omega_using [hk2, ek, hB, hRs, hi]), shV_eq _ (by omega_using [hk2, ek, hidx']) (fun x h₁ h₂ => by
      rw [hT x (by omega_using [hk2, ek, h₂])]; simp [srcB, List.getD_eq_getElem?_getD, show ¬ x < kk s - (2 * D + 1) by omega_using [h₁]]) hi]
    by_cases hl : i + (idx + 1) < kk s
    · rw [ifp hl, hT _ (by omega_using [hk2, ek, hidx', hi])]
    · rw [ifn hl]; simp [srcB, List.getD_eq_getElem?_getD, show ¬ i + (idx + 1) < kk s - (2 * D + 1) by omega_using [hl]]
  -- `out`, `*msg_len` and the result.
  have hu : ∀ x, ¬ (mlR s).Contains x 1 → u.mem x = t₉.mem x := fun x hx => by
    rw [mu]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self (mlR s)) _ (Region.contains_self _ _)) x
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hx)
  have hlen : ((Spec.Rsa.bytesAt t₈.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t₈.gpr .r26)).length =
      kk s := by simp [bytesAt_length]
  have hout : ∀ i < kk s, u.mem (s.gpr .r3 + BitVec.ofNat 64 i) =
      andB ((srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD (i + (idx + 1)) 0) (t₉.gpr .r26) := by
    intro i hi
    rw [hu _ (fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega_using [ek, hi, this]) (by omega_using [ek, hi])) hc), m₉]
    rw [writeBytes_at _ _ _ (by rw [hlen]; exact hi) (by rw [hlen]; omega_using [ek]), List.getD_eq_getElem?_getD,
      List.getElem?_map, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some, Option.getD_some]
    rw [g₉ .r26 (by simp)]
    congr 1
    rw [m₈, ← hbuf i hi]; show t₇.mem (off (off (Sd s) oBuf) i) = _; rw [off_off]; rfl
  have hml : u.mem.readW (s.gpr .r5) 64 = (BitVec.ofNat 64 (kk s) - BitVec.ofNat 64 (2 * D + 2) -
      BitVec.ofNat 64 idx) &&& t₉.gpr .r26 := by
    rw [mu, Mem.readW_writeW_self64, show s.gpr .r7 = BitVec.ofNat 64 (kk s) from
      (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm]
  rw [hok] at hout hml ru

  exact dec_written hGv hHv hHl (by omega_using [hk]) hk2 v₁ hlh (fun em he => by
      have := A.em; rw [hO, he] at this; exact this.symm)
    hidx (by rcases hidx' with h | h; exact .inl h; exact .inr h) hout hml (by rw [ru, hRC])

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end


/-!
# RSAES-OAEP decryption on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The entry, the private
operation (`priv_ok`), the check of `k ≥ 2 hLen + 2` (public), then either
zeros and the result `r = 2 ? 2 : 0` (`decFail_ok`, which is what `decOut`
says for a too short `k`) or the decoding (`decMain_ok`), and the restores:
RSAES-OAEP-DECRYPT (RFC 8017 §7.1.2), with MGF1's hash function the
table's. `code_correct`: the function against its contract, for the tables
of `vs` (`tab_ofD`: the table is one of them, whose hash function it
names).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_sub wp_lsr wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes)
open VG.Proof.RsaOaep (decOut decOut_short)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.MdHashTable.PPC64LE (MVar tables fns3 Coh)

/-- The result and the outputs, from the entry state `s`. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ Spec.RsaOaep.writtenDecrypt s'.mem (s.gpr .r3) (s.gpr .r5) (kk s) ((s'.gpr .r3).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ Spec.RsaOaep.writtenDecrypt t.mem (s.gpr .r3) (s.gpr .r5) (kk s) ((t.gpr .r3).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

theorem AfterPriv.only {pc : Bool} {s v v' : State} {rs : List Reg} (A : AfterPriv s v) (P : PreD pc s) (o : Only rs v v')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : AfterPriv s v' := by
  have hm : v'.mem = v.mem := o.mem
  have b := A.base
  rw [← hm] at b
  exact ⟨b.only (fitsM P) o hrs, hm ▸ A.mem, hm ▸ A.em⟩

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem decTail_D {G G' : Hash} (hD : G.D = G'.D) (f : Fns) : decTail G f = decTail G' f := by
  simp only [Dec.decTail, Dec.decMain, Dec.chkK, Dec.accLh, Dec.scan, Dec.tArgs, Dec.copyT, Dec.decRet, seedArgs,
    dbArgs, hD]

/-- `EM` too short for the hash: what decryption returns, from the private
operation's result. -/
theorem decOut_short' {Hs Gs : Spec.Mgf1.Hash} {lab : List Byte} {o : Spec.Rsa.Outcome} {k : Nat}
    (hl : ∀ em, o = .ok em → em.length = k) (hk : k < 2 * Hs.len + 2) :
    decOut Hs Gs lab o = if rcOf o = 2 then .fault else .invalid := by
  rw [decOut_short hl hk]
  cases o <;> rfl

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
  {pc : Bool} {f : Fns} {s : State} (P : PreD pc s) (T : TabS G f 16 (SD s) s (stackArg s 16))
  (TL : TabS H f 15 (SD s) s (stackArg s 15))
include hH hG hHh hHl hHv hGh hGl hGv P T TL

omit hH hG hHh hHv hGh hGl hGv T TL in
theorem fail_done {v : State} (A : AfterPriv s v) (hk : kk s < 2 * H.D + 2) :
    WP isa decFail v (Done Hs Gs s) := by
  have hrc := rcOf_le (privO s)
  refine WP.mono (decFail_ok P A.base hrc) fun u ⟨sv, _, hm, h3⟩ => ⟨sv, ?_⟩
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have hl : ∀ em, privO s = .ok em → em.length = kk s := fun em he => by
    have := A.em; rw [he] at this; simp only [emOf] at this; rw [← this, bytesAt_length]
  rw [decOut_short' hl (by rw [hHl]; exact hk)]
  have hout : Spec.Rsa.bytesAt u.mem (s.gpr .r3) (kk s) = List.replicate (kk s) 0 := by
    have e := bytesAt_writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0)
      (by rw [List.length_replicate]; omega_using [ek])
    rw [List.length_replicate] at e
    rw [← e, hm]
    have f : Frame [mlR s] (writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0))
        ((writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0)).writeW (s.gpr .r5) (0#64)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact f _ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega_using [ek, hi, this]) (by omega_using [ek, hi])) hc)
  have hml : u.mem.readW (s.gpr .r5) 64 = 0 := by rw [hm, Mem.readW_writeW_self64]; rfl
  have hrc2 := rcOf_le (privO s)
  by_cases h2 : rcOf (privO s) = 2
  · rw [ifp h2]; exact ⟨by rw [h3, ifp h2]; decide, hout, hml⟩
  · rw [ifn h2]; exact ⟨by rw [h3, ifn h2]; decide, hout, hml⟩

omit hH hG hHh hHl hHv hGh hGl hGv T TL in
/-- The check of `k`: in `r3`, whether it is too short. -/
theorem chk_ok (hD64 : H.D ≤ 64) {v : State} (A : AfterPriv s v) :
    WP isa (.block (Dec.chkK H)) v fun v' => AfterPriv s v' ∧ (v'.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2) := by
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have e7 : s.gpr .r7 = BitVec.ofNat 64 (kk s) := ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  refine wp_li (by omega_using [hD64]) fun v₁ o₁ e₁ => wp_sub fun v₂ o₂ e₂ => wp_lsr fun v₃ o₃ e₃ => wp_nil ?_
  have k₃ : Only [.r3] v v₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨A.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, o₁.get .r15, Base.r15 A.base, e7]
  exact ne_zero_ltBit (by omega_using [hk2, ek]) (by omega_using [hD64])

/-- The branch on the check of `k`. -/
theorem ite_done {v : State} (A : AfterPriv s v) (hsy : v.syms = s.syms)
    (r3 : (v.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2)) :
    WP isa (.ite (.nonzero .d .r3) decFail (decMain H f)) v (Done Hs Gs s) :=
  WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P A (by rw [r3] at hc; simpa using hc))
    (fun hc => WP.mono (decMain_ok P hH hG hHh hHl hHv hGh hGl hGv T TL A hsy (by rw [r3] at hc; simp at hc; omega_using [hc]))
      fun u ⟨sv, _, hw⟩ => ⟨sv, hw⟩)

theorem checks_done {v : State} (A : AfterPriv s v) (hsy : v.syms = s.syms) :
    WP isa (.block (Dec.chkK H)) v fun v' =>
      WP isa (.ite (.nonzero .d .r3) decFail (decMain H f)) v' (Done Hs Gs s) :=
  WP.mono_syms (chk_ok P hH.hD64 A) fun _ ⟨A', r3⟩ y => ite_done hH hG hHh hHl hHv hGh hGl hGv P T TL A' (y.trans hsy) r3

theorem code_ok (X : pc = true → PreXD s) (hl : H.D ∈ lens) : WP isa (decryptG pc f) s (Post Hs Gs s) := by
  have hD64 := hH.hD64
  refine WP.alloc (by decide) (by have := P.sp1; rw [stackBytes_eq] at this; unfold frameBytes; omega_using [this]) ?_
  refine WP.seq (WP.mono_syms (entry_ok P) fun t E y₁ => ?_)
  refine WP.seq (WP.mono_syms (priv_ok P X E) fun v A y₂ => ?_)
  -- The label's hash function's digest length to `r3`.
  have TL' := tabS_wmL P TL A.mem
  refine WP.seq (WP.of_syms ?_)
  show WP isa (.block (tword .r3 15 6 ++ [])) v _
  refine wp_tword TL' A.base (k := 6) (by decide) (d := .r3) (by decide) fun v₁ o₁ e₁ => wp_nil fun y₃ => ?_
  have e3 : v₁.gpr .r3 = BitVec.ofNat 64 H.D := e₁.trans TL'.d
  -- The code for that length.
  refine WP.seq (byLen_ok (D := H.D) (by omega_using [hD64])
    (F := fun u => AfterPriv s u ∧ u.syms = s.syms ∧ u.gpr .r3 = BitVec.ofNat 64 H.D)
    (fun _ h => h.2.2) (fun u u' ⟨A', y', r3'⟩ o y => ⟨A'.only P o, y.trans y', by rw [o.get .r3]; exact r3'⟩) ?_
    hl (fun x hx => (lens_certs x hx).1) v₁ ⟨A.only P o₁, y₃.trans (y₂.trans y₁), e3⟩)
  intro u ⟨A', y', _⟩
  rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
  exact WP.seq (WP.mono (checks_done hH hG hHh hHl hHv hGh hGl hGv P T TL A' y') fun v' h => WP.mono h
    fun t' ⟨sv, res⟩ => WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ => ⟨habi, by
      rw [freed_mem, freed_gpr, hm, h3]; exact res⟩)

end

/-- The label's hash function's table, on entry, if it is `w`'s: what its
calls need of it. -/
theorem tabS_entryDL {vs : List MVar} (hc : Coh vs) {pc : Bool} {s : State} (P : PreD pc s)
    (hpw : (Proof.MdHashTable.PPC64LE.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : MVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (Proof.MdHashTable.PPC64LE.tableOf w))) :
    TabS w.H (fns3 vs) 15 (SD s) s (stackArg s 15) := by
  refine Proof.MdHashTable.PPC64LE.tabS_of (by decide) rfl (A := aR pc s) (by rw [P.hrd]; exact aR_mem)
    (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; exact List.mem_append_right _ (List.mem_cons_self ..)) (P.ktl.sub_left kR_sub)
    (P.stl.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by split <;> omega_using [])

/-- MGF1's table, on entry, if it is `w`'s: what MGF1 needs of it. -/
theorem tabS_entryD {vs : List MVar} (hc : Coh vs) {pc : Bool} {s : State} (P : PreD pc s)
    (hpw : (Proof.MdHashTable.PPC64LE.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : MVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s (Proof.MdHashTable.PPC64LE.tableOf w))) :
    TabS w.H (fns3 vs) 16 (SD s) s (stackArg s 16) := by
  refine Proof.MdHashTable.PPC64LE.tabS_of (by decide) rfl (A := aR pc s) (by rw [P.hrd]; exact aR_mem)
    (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (P.kt.sub_left kR_sub)
    (P.st.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by split <;> omega_using [])

/-- The tables, on entry: each one of the tables of `vs`, which names its
hash function and holds what the calls through it need. -/
theorem tab_ofD {vs : List MVar} (hc : Coh vs) {s : State} (h : (decSpec (tables vs)).pre s) :
    ∃ w₁ ∈ vs, ∃ w ∈ vs, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some w₁.l.G ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some w.l.G ∧
      TabS w₁.H (fns3 vs) 15 (SD s) s (stackArg s 15) ∧ TabS w.H (fns3 vs) 16 (SD s) s (stackArg s 16) := by
  obtain ⟨⟨T₁, hT₁, hh₁⟩, ⟨T, hT, hh⟩, hpw⟩ := spec_tabD h
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  have P := preD_of h
  exact ⟨w₁, hw₁, w, hw, Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh₁).2.2.2,
    Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh).2.2.2,
    tabS_entryDL hc P hpw' hw₁ hh₁, tabS_entryD hc P hpw' hw hh⟩

/-- The correctness of `vg_rsa_oaep_decrypt`, against its contract, for the
tables of `vs`. -/
theorem code_correct {vs : List MVar} (hc : Coh vs) (s : State) (h : (decSpec (tables vs)).pre s) :
    ∃ t s', Exec isa (decrypt (fns3 vs)) s t s' ∧ abiPreserved s s' ∧ (decSpec (tables vs)).post s s' := by
  obtain ⟨w₁, -, w, -, hH, hG, TL, T⟩ := tab_ofD hc h
  have P : PreD false s := preD_of h
  obtain ⟨t, s', he, habi, hr⟩ := code_ok w₁.l.ok w.l.ok w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len w.l.valid
    P T TL nofun w₁.l.lens_mem
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpec
  rw [e]
  sig_post [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Abi.withTables, abi, argRegs, stackArgs_seventeen, List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [Proof.RsaOaep.decrypt_eq (by rw [bytesAt_length, bytesAt_length])]
  exact hr

end VG.Proof.RsaOaep.PPC64LE.Dec
