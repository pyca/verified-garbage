module

public import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Tables
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBlocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCorrect
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTTab
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Unmask
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Buf
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Out
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Scan
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Shift
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Written
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaOaep.Decode
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfStepsT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith

/-! ### `RsaOaep.PPC64LE.Dc.CTMain`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.PPC64LE.Dc.Correct`, which this module and modules that import it used -/

section

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
  obtain hrc := rcOf_le (privO s)
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
  obtain h25 : t₆.gpr .r25 = BitVec.ofNat 64 idx := by
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
  obtain hS : ∀ {x}, x < oSt → ∀ p ∈ [(oSt, H.S), (oDig, H.FD), (oW, H.W)], x < p.1 ∨ p.1 + p.2 ≤ x :=
    fun hx p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact .inl (by simp only; omega_arith)
  obtain e2 : ∀ x < oSt, view t₂.mem (Sd s) x = view t₁.mem (Sd s) x := fun x hx => s₂ x (by omega_using [hSt, hRs, hx]) (hS hx)
  obtain hlab : Spec.Rsa.bytesAt v.mem (stackArg s 9) (stackArg s 10).toNat = labB s := labB_eq P A.mem
  rw [hlab] at h₂
  obtain hlh : ∀ i < D, view t₂.mem (Sd s) (oDig + i) = (Hs.hash (labB s)).getD i 0 := fun i hi => by
    have := congrArg (fun l => l.getD i 0) h₂
    rw [bytesAt_view, srcB, map_range_getD' _ (by omega_using [hDF, hi])] at this
    rw [this, hHh, hH.hashTake]
    simp [List.getD_eq_getElem?_getD, show i < H.D by omega_using [hD, hi]]
  -- `lHash'`, `lHash` and the scan, on the view after unmasking.
  obtain hc0 : t₃.gpr .r24 = accG (view t₁.mem (Sd s) 0) (fun i => view t₁.mem (Sd s) (1 + D + i))
      (fun i => view t₂.mem (Sd s) (oDig + i)) D := by
    rw [a₃, e2 0 (by omega_using [hSt])]
    exact accG_congr _ D (fun i hi => e2 _ (by omega_using [hFD, hSt, hDF, hi])) (fun _ _ => rfl)
  obtain hsc' : sc = scanS (fun i => view t₁.mem (Sd s) (1 + 2 * D + i)) (accG (view t₁.mem (Sd s) 0)
      (fun i => view t₁.mem (Sd s) (1 + D + i)) (fun i => view t₂.mem (Sd s) (oDig + i)) D) (kk s - (2 * D + 1)) := by
    rw [← hsc, hc0, m₃]
    exact scanS_congr _ _ fun i hi => e2 _ (by omega_using [hk2, ek, hSt, hi])
  rw [hsc'] at hidx
  obtain r24 : t₇.gpr .r24 = sc.2.2 ||| sc.1 := by
    rw [k₇.get .r24, g₆ .r24 (by simp), g₅ .r24 (by simp), a₄]
  obtain hok : t₉.gpr .r26 = mk (rcOf o = 1 ∧ (sc.2.2 ||| sc.1) = 0) := by
    rw [g₉ .r26 (by simp), o₈, r24, ← hRC]
  rw [hsc'] at hok
  -- The buffer.
  obtain hT : ∀ y < 2048, view t₆.mem (Sd s) (oBuf + y) =
      (srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD y 0 := by
    intro y hy
    rw [v₆ _ (by omega_using [hB, hRs, hy])]
    by_cases hyt : y < kk s - (2 * D + 1)
    · rw [ifp ⟨by omega_using [], by omega_using [hyt]⟩, show oBuf + y - oBuf = y by omega_using [], v₅ _ (by omega_using [hFD, hRs, hDF, hy]), ifn (by omega_using [hFD, hB, hDF, hy]), m₄, m₃,
        e2 _ (by omega_using [hk2, ek, hSt, hyt]), srcB, map_range_getD' _ hyt]
    · rw [ifn (by omega_using [hyt]), v₅ _ (by omega_using [hB, hRs, hy]), ifp ⟨by omega_using [], by omega_using [hy]⟩]
      simp [srcB, List.getD_eq_getElem?_getD, hyt]
  obtain hbuf : ∀ i < kk s, view t₇.mem (Sd s) (oBuf + i) =
      (srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD (i + (idx + 1)) 0 := by
    intro i hi
    rw [v₇ _ (by omega_using [hk2, ek, hB, hRs, hi]), shV_eq _ (by omega_using [hk2, ek, hidx']) (fun x h₁ h₂ => by
      rw [hT x (by omega_using [hk2, ek, h₂])]; simp [srcB, List.getD_eq_getElem?_getD, show ¬ x < kk s - (2 * D + 1) by omega_using [h₁]]) hi]
    by_cases hl : i + (idx + 1) < kk s
    · rw [ifp hl, hT _ (by omega_using [hk2, ek, hidx', hi])]
    · rw [ifn hl]; simp [srcB, List.getD_eq_getElem?_getD, show ¬ i + (idx + 1) < kk s - (2 * D + 1) by omega_using [hl]]
  -- `out`, `*msg_len` and the result.
  obtain hu : ∀ x, ¬ (mlR s).Contains x 1 → u.mem x = t₉.mem x := fun x hx => by
    rw [mu]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self (mlR s)) _ (Region.contains_self _ _)) x
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hx)
  obtain hlen : ((Spec.Rsa.bytesAt t₈.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t₈.gpr .r26)).length =
      kk s := by simp [bytesAt_length]
  obtain hout : ∀ i < kk s, u.mem (s.gpr .r3 + BitVec.ofNat 64 i) =
      andB ((srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD (i + (idx + 1)) 0) (t₉.gpr .r26) := by
    intro i hi
    rw [hu _ (fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega_using [ek, hi, this]) (by omega_using [ek, hi])) hc), m₉]
    rw [writeBytes_at _ _ _ (by rw [hlen]; exact hi) (by rw [hlen]; omega_using [ek]), List.getD_eq_getElem?_getD,
      List.getElem?_map, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some, Option.getD_some]
    rw [g₉ .r26 (by simp)]
    congr 1
    rw [m₈, ← hbuf i hi]; show t₇.mem (off (off (Sd s) oBuf) i) = _; rw [off_off]; rfl
  obtain hml : u.mem.readW (s.gpr .r5) 64 = (BitVec.ofNat 64 (kk s) - BitVec.ofNat 64 (2 * D + 2) -
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
  obtain hrc := rcOf_le (privO s)
  refine WP.mono (decFail_ok P A.base hrc) fun u ⟨sv, _, hm, h3⟩ => ⟨sv, ?_⟩
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  obtain hl : ∀ em, privO s = .ok em → em.length = kk s := fun em he => by
    have := A.em; rw [he] at this; simp only [emOf] at this; rw [← this, bytesAt_length]
  rw [decOut_short' hl (by rw [hHl]; exact hk)]
  obtain hout : Spec.Rsa.bytesAt u.mem (s.gpr .r3) (kk s) = List.replicate (kk s) 0 := by
    obtain e := bytesAt_writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0)
      (by rw [List.length_replicate]; omega_using [ek])
    rw [List.length_replicate] at e
    rw [← e, hm]
    obtain f : Frame [mlR s] (writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0))
        ((writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0)).writeW (s.gpr .r5) (0#64)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    exact f _ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega_using [ek, hi, this]) (by omega_using [ek, hi])) hc)
  obtain hml : u.mem.readW (s.gpr .r5) 64 = 0 := by rw [hm, Mem.readW_writeW_self64]; rfl
  obtain hrc2 := rcOf_le (privO s)
  by_cases h2 : rcOf (privO s) = 2
  · rw [ifp h2]; exact ⟨by rw [h3, ifp h2]; decide, hout, hml⟩
  · rw [ifn h2]; exact ⟨by rw [h3, ifn h2]; decide, hout, hml⟩

omit hH hG hHh hHl hHv hGh hGl hGv T TL in
/-- The check of `k`: in `r3`, whether it is too short. -/
theorem chk_ok (hD64 : H.D ≤ 64) {v : State} (A : AfterPriv s v) :
    WP isa (.block (Dec.chkK H)) v fun v' => AfterPriv s v' ∧ (v'.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2) := by
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  obtain e7 : s.gpr .r7 = BitVec.ofNat 64 (kk s) := ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  refine wp_li (by omega_using [hD64]) fun v₁ o₁ e₁ => wp_sub fun v₂ o₂ e₂ => wp_lsr fun v₃ o₃ e₃ => wp_nil ?_
  obtain k₃ : Only [.r3] v v₃ := (o₁.trans (o₂.trans o₃)).mono
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
  obtain TL' := tabS_wmL P TL A.mem
  refine WP.seq (WP.of_syms ?_)
  show WP isa (.block (tword .r3 15 6 ++ [])) v _
  refine wp_tword TL' A.base (k := 6) (by decide) (d := .r3) (by decide) fun v₁ o₁ e₁ => wp_nil fun y₃ => ?_
  obtain e3 : v₁.gpr .r3 = BitVec.ofNat 64 H.D := e₁.trans TL'.d
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
  obtain hpw' := hpw.sublist (List.sublist_append_left _ _)
  obtain P := preD_of h
  exact ⟨w₁, hw₁, w, hw, Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh₁).2.2.2,
    Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh).2.2.2,
    tabS_entryDL hc P hpw' hw₁ hh₁, tabS_entryD hc P hpw' hw hh⟩

/-- The correctness of `vg_rsa_oaep_decrypt`, against its contract, for the
tables of `vs`. -/
theorem code_correct {vs : List MVar} (hc : Coh vs) (s : State) (h : (decSpec (tables vs)).pre s) :
    ∃ t s', Exec isa (decrypt (fns3 vs)) s t s' ∧ abiPreserved s s' ∧ (decSpec (tables vs)).post s s' := by
  obtain ⟨w₁, -, w, -, hH, hG, TL, T⟩ := tab_ofD hc h
  obtain P : PreD false s := preD_of h
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

end

end

/-! ### `RsaOaep.PPC64LE.Dc.CTBase`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: two runs

Untrusted: everything here is checked by Lean. Two runs are compared through
an anchor `a`, the first run's entry state: `PubD a s` says the entry state
`s` has `a`'s public data (`pubD_of`, from the shared contract's). After the
private operation, `DX a t` says `t` has `Base` for the decoding from such an
entry state, whose working space and `k`, `out`, `msg_len` and the label in
`r14`–`r19` are then `a`'s (`DX.pins`), while `r20` holds that run's own
result. The shared code compares runs whose `Base` has the same functions
of the base state: the working space at `stackArg x 13` (`SX`) and the
values of `r15`–`r23` read from `x`, with the result in its `r0` (`VX`); the
base state of a run is its entry state with the memory after the private
operation and the result in `r0` (`bx`, `toX`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Pins)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The shared contract's public data, by name. -/
structure PubD (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = a.gpr r
  args : ∀ i < 17, stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r6) (a.gpr .r7).toNat
  e : Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat

/-- The contract's public data: `PubD`, the tables' functions at the same
addresses, and the same tables held at both tables' addresses. -/
theorem pubD_of {ts : List FnTable} {s₁ s₂ : State} (h : (decSpec ts).pub s₁ s₂) :
    PubD s₁ s₂ ∧ (∀ f ∈ (ts.map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 16) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 16) (FnTable.words isa s₂ T)) := by
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpec at h
  rw [e] at h
  sig_pub [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_seventeen, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htabL, htab, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16⟩ := h
  simp only [List.map_append] at hl
  obtain ⟨hn, he⟩ := List.append_inj hl (by simp [bytesAt_length, h7])
  have inj := fun {x y : List Byte} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm⟩,
    fun f hf => hsy f (List.mem_append_left _ hf), fun T hT => htabL _ _ rfl rfl T hT,
    fun T hT => htab _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm, a13.symm, a14.symm, a15.symm, a16.symm]

theorem pubD_refl (s : State) : PubD s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- With `pc`, `pre`'s public data: its address, its length and what the
call may leak of it. -/
def PubP (a s : State) : Prop :=
  stackArg s 17 = stackArg a 17 ∧ stackArg s 18 = stackArg a 18 ∧
    Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .r7).toNat =
      Spec.Rsa.privatePrecomputedLeak a.mem (stackArg a 17) (a.gpr .r7).toNat

/-- With `pc`, `pre`'s facts and public data. -/
abbrev XP (pc : Bool) (a s : State) : Prop := pc = true → PreXD s ∧ PubP a s

/-! ## The base state for the shared code -/

/-- The entry state `s` with memory `m` and `rc` in `r0`. -/
def bx (s : State) (m : Mem) (rc : Nat) : State :=
  { s with mem := m, gpr := fun r => if r = .r0 then BitVec.ofNat 64 rc else s.gpr r }

/-- The working space, of the base state. -/
abbrev SX : State → Addr := fun x => stackArg x 13

/-- `r15`–`r23`, of the base state. -/
def VX (x : State) : Reg → BitVec 64 := vD x (x.gpr .r0).toNat

/-- What the shared code needs of the base state. -/
def PreX (x : State) : Prop := Fits SX x

/-- The base state's public data: the stack pointer and the working space. -/
def PubX (a x : State) : Prop := x.sp = a.sp ∧ stackArg x 13 = stackArg a 13

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} (hm : Frame [kD s, scR s] s.mem m) (rc : Nat)
include P hm

/-- The stack arguments, in the base state. -/
theorem stackArg_bx {i : Nat} (hi : i < 17) : stackArg (bx s m rc) i = stackArg s i := by
  show m.readW (stackArgAddr s i) 64 = s.mem.readW (stackArgAddr s i) 64
  exact hm.readW (in_aR hi) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact P.ka.symm
    · exact P.sa.symm) (by decide)

/-- `Base` for the shared code, from the decoding's. -/
theorem toX (hrc : rc ≤ 2) {t : State} (b : Base (SD s) (VD s rc) (withMem s m) t) :
    PreX (bx s m rc) ∧ Base SX VX (bx s m rc) t := by
  have h13 : SX (bx s m rc) = Sd s := stackArg_bx P hm rc (i := 13) (by decide)
  have g : ∀ r, r ≠ .r0 → (bx s m rc).gpr r = s.gpr r := fun r hr => by simp [bx, hr]
  have f := fits P (s' := bx s m rc) rfl rfl
  have eSC : SC SX (bx s m rc) = SC (SD s) (withMem s m) := by simp only [SC, h13]
  refine ⟨⟨f.sp1, by rw [h13]; exact f.sc, by rw [eSC]; exact f.ksc, by rw [h13]; exact f.wS⟩,
    ⟨⟨b.sv.sp, b.sv.wr, fun r hr => by rw [g r (by revert r; decide)]; exact b.sv.hi r hr,
      fun p hp => (b.sv.sv p hp).trans (g p.1 (by revert p; decide)).symm, b.sv.ls⟩, b.rd, b.r14.trans h13.symm,
      fun r hr => ?_, by rw [eSC]; exact b.mem⟩⟩
  have e0 : ((bx s m rc).gpr .r0).toNat = rc := by
    show (BitVec.ofNat 64 rc).toNat = rc
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hrc])]
  rw [b.vs r hr]
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [VX, vD, e0, g _ (show Reg.r7 ≠ .r0 by decide), g _ (show Reg.r3 ≠ .r0 by decide),
      g _ (show Reg.r5 ≠ .r0 by decide), g _ (show Reg.r21 ≠ .r0 by decide), g _ (show Reg.r22 ≠ .r0 by decide),
      g _ (show Reg.r23 ≠ .r0 by decide), stackArg_bx P hm rc (i := 9) (by decide),
      stackArg_bx P hm rc (i := 10) (by decide)]

end

/-! ## After the private operation -/

/-- `t` has the decoding's `Base` from an entry state with `a`'s public data. -/
def DX (a t : State) : Prop :=
  ∃ pc s m, PreD pc s ∧ PubD a s ∧ Frame [kD s, scR s] s.mem m ∧
    Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t

/-- What `DX` fixes, from the anchor. -/
theorem DX.pins {a t : State} (h : DX a t) :
    t.sp = fb a ∧ t.gpr .r14 = stackArg a 13 ∧ t.gpr .r15 = a.gpr .r7 ∧ t.gpr .r16 = a.gpr .r3 ∧
      t.gpr .r17 = a.gpr .r5 ∧ t.gpr .r18 = stackArg a 9 ∧ t.gpr .r19 = stackArg a 10 := by
  obtain ⟨_, s, m, P, p, hm, b⟩ := h
  exact ⟨by rw [b.sp]; show fb s = fb a; rw [fb, fb, p.sp], b.r14.trans (p.args 13 (by decide)),
    by rw [Base.r15 b, p.g _ (by decide)], by rw [Base.r16 b, p.g _ (by decide)], by rw [Base.r17 b, p.g _ (by decide)],
    by rw [Base.r18 b, p.args 9 (by decide)], by rw [Base.r19 b, p.args 10 (by decide)]⟩

/-- The registers `DX` fixes are the same in both runs. -/
theorem dx_pins {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → DX (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ [Reg.r14, .r15, .r16, .r17, .r18, .r19] := by decide) : Pins Φ rs :=
  fun x t₁ t₂ h₁ h₂ => by
    obtain ⟨s₁, a₁, b₁, c₁, d₁, e₁, f₁⟩ := (h x t₁ h₁).pins
    obtain ⟨s₂, a₂, b₂, c₂, d₂, e₂, f₂⟩ := (h x t₂ h₂).pins
    refine ⟨s₁.trans s₂.symm, fun r hr => ?_⟩
    have := hrs r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm, d₁.trans d₂.symm, e₁.trans e₂.symm,
      f₁.trans f₂.symm]

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-! ### `RsaOaep.PPC64LE.Dc.CTLabel`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: the shared code's base state

Untrusted: everything here is checked by Lean. The shared code's base state
has the entry's public data (`pubX_bx`); the label's hash is through its table,
in two runs `hashLabelT_ct` (`Proof/RsaPss/PPC64LE/CTTab.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two two_post wp_li wp_addi wp_mov wp_nil)

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} (hm : Frame [kD s, scR s] s.mem m) {rc : Nat} (hrc : rc ≤ 2)
include P hm hrc

omit hrc in
theorem pubX_bx {a : State} (p : PubD a s) : PubX a (bx s m rc) :=
  ⟨p.sp, (stackArg_bx P hm rc (by decide)).trans (p.args 13 (by decide))⟩

end

theorem off13 {a s : State} (p : PubD a s) (o : Nat) : off (stackArg a 13) o = off (Sd s) o := by
  show off (stackArg a 13) o = off (stackArg s 13) o
  rw [p.args 13 (by decide)]

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-! ### `RsaOaep.PPC64LE.Dc.CTPriv`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: the private operation, twice

Untrusted: everything here is checked by Lean. `priv_ct`: two runs of the
private operation from entry states with the same public data leak alike:
its frame's arguments by the taint analysis, and the call of
`vg_rsa_private_checked` by its constant time (`RelCT.callEx`), whose public
data at the call (`priv_pub`) are the entry's: the pointers and lengths, the
modulus and the public exponent. Its result then differs between the runs,
in `r20` (`DX`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_alloc)

theorem psa_pub {a s : State} (p : PubD a s) {i : Nat} (hi : i < 12) : psa s i = psa a i := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [psa, Sd, p.g .r10 (by decide), p.args _ (by decide : (0 : Nat) < 17),
      p.args _ (by decide : (1 : Nat) < 17), p.args _ (by decide : (2 : Nat) < 17),
      p.args _ (by decide : (3 : Nat) < 17), p.args _ (by decide : (4 : Nat) < 17),
      p.args _ (by decide : (5 : Nat) < 17), p.args _ (by decide : (6 : Nat) < 17),
      p.args _ (by decide : (7 : Nat) < 17), p.args _ (by decide : (8 : Nat) < 17),
      p.args _ (by decide : (13 : Nat) < 17), p.args _ (by decide : (14 : Nat) < 17)]

/-- At the call, from an entry state with `a`'s public data. -/
def APriv (pc : Bool) (a u : State) : Prop := ∃ s, PreD pc s ∧ PubD a s ∧ AtPriv pc s u ∧ XP pc a s

/-- The public data at the call, but `pre`'s leak. -/
theorem priv_facts {pc : Bool} {a s₁ s₂ u₁ u₂ : State} (P₁ : PreD pc s₁) (p₁ : PubD a s₁) (A₁ : AtPriv pc s₁ u₁)
    (P₂ : PreD pc s₂) (p₂ : PubD a s₂) (A₂ : AtPriv pc s₂ u₂) :
    (callE pc s₁ u₁).sp = (callE pc s₂ u₂).sp ∧
      (∀ r ∈ argRegs, (callE pc s₁ u₁).gpr r = (callE pc s₂ u₂).gpr r) ∧
      (∀ i < 12, stackArg (callE pc s₁ u₁) i = stackArg (callE pc s₂ u₂) i) ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r5) ((callE pc s₁ u₁).gpr .r6).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r5) ((callE pc s₂ u₂).gpr .r6).toNat ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r7) ((callE pc s₁ u₁).gpr .r8).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r7) ((callE pc s₂ u₂).gpr .r8).toNat := by
  have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
  have hb := fun {s u : State} (A : AtPriv pc s u) {p : Addr} {len : Nat}
    (hd : (kD s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hl
  refine ⟨by rw [callE_sp, callE_sp, A₁.sp, A₂.sp, pb, pb, fb, fb, p₁.sp, p₂.sp], fun r hr => ?_,
    fun i hi => by rw [callE_stackArg A₁ (lt_nCall hi), callE_stackArg A₂ (lt_nCall hi), psa_pub p₁ hi,
      psa_pub p₂ hi], ?_, ?_⟩
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, Sd, Sd, p₁.args 13 (by decide), p₂.args 13 (by decide)]
    · rw [A₁.r4, A₂.r4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r5, A₂.r5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r6, A₂.r6, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r7, A₂.r7, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r8, A₂.r8, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r9, A₂.r9, p₁.args 11 (by decide), p₂.args 11 (by decide)]
    · rw [A₁.r10, A₂.r10, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [m, m, callE_gpr _ _ (r := .r5), callE_gpr _ _ (r := .r6), callE_gpr _ _ (r := .r5),
      callE_gpr _ _ (r := .r6), A₁.r5, A₁.r6, A₂.r5, A₂.r6, hb A₁ P₁.kn (by have := P₁.wn; omega_using []),
      hb A₂ P₂.kn (by have := P₂.wn; omega_using []), p₁.n, p₂.n]
  · rw [m, m, callE_gpr _ _ (r := .r7), callE_gpr _ _ (r := .r8), callE_gpr _ _ (r := .r7),
      callE_gpr _ _ (r := .r8), A₁.r7, A₁.r8, A₂.r7, A₂.r8, hb A₁ P₁.ke (by have := P₁.we; omega_using []),
      hb A₂ P₂.ke (by have := P₂.we; omega_using []), p₁.e, p₂.e]

/-- With `pc`, the call's two more stack arguments, `pre` and `pre_len`, are
the anchor's. -/
theorem psa_pubP {a s : State} (x : PubP a s) {i : Nat} (hi : 12 ≤ i) (hi' : i < 14) : psa s i = psa a i := by
  rcases (by omega_using [hi, hi'] : i = 12 ∨ i = 13) with rfl | rfl
  · exact x.1
  · exact x.2.1

/-- With `pc`, what the call may leak of `pre`, as on entry. -/
theorem pre_leak {s u : State} (X : PreXD s) (A : AtPriv true s u) :
    Spec.Rsa.privatePrecomputedLeak (callE true s u).mem (stackArg (callE true s u) 12)
        ((callE true s u).gpr .r6).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .r7).toNat := by
  have pwl : Spec.Rsa.precomputedWords (s.gpr .r7).toNat ≤ (stackArg s 18).toNat := by
    rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide), psa,
    callE_gpr (pc := true) s u (r := .r6), A.r6]
  congr 1
  have subPre : Region.Sub ⟨stackArg s 17, 8 * Spec.Rsa.precomputedWords (s.gpr .r7).toNat⟩ (preR s) :=
    fun _ hx => by simp only [Region.Contains] at hx ⊢; omega_using [pwl, hx]
  exact VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact X.kP.symm.sub_left subPre) (by have := X.wP; omega_using [pwl, this])

theorem call_ct (pc : Bool) : RelCT isa (Two (APriv pc)) (privCall pc) fun _ _ => True := by
  cases pc with
  | false =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      Rsa.PPC64LE.Priv.code_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, P₁, p₁, A₁, -⟩ := h₁
    obtain ⟨s₂, P₂, p₂, A₂, -⟩ := h₂
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts P₁ p₁ A₁ P₂ p₂ A₂
    exact ⟨callRd false s₁, callWr s₁, callRd false s₂, callWr s₂, Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₂ A₂), Rsa.PPC64LE.Priv.pub_of hsp hr ha hn he,
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
  | true =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      Rsa.PPC64LE.Priv.codeP_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, P₁, p₁, A₁, x₁⟩ := h₁
    obtain ⟨s₂, P₂, p₂, A₂, x₂⟩ := h₂
    obtain ⟨X₁, q₁⟩ := x₁ rfl
    obtain ⟨X₂, q₂⟩ := x₂ rfl
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts P₁ p₁ A₁ P₂ p₂ A₂
    refine ⟨callRd true s₁, callWr s₁, callRd true s₂, callWr s₂,
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₁ A₁) (preX_at P₁ X₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₂ A₂) (preX_at P₂ X₂ A₂),
      Rsa.PPC64LE.Priv.pub_ofP hsp hr (fun i hi => ?_) hn he
        (by rw [pre_leak X₁ A₁, pre_leak X₂ A₂, q₁.2.2, q₂.2.2]),
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
    by_cases h12 : i < 12
    · exact ha i h12
    · rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, psa_pubP q₁ (by omega_using [h12]) hi, psa_pubP q₂ (by omega_using [h12]) hi]

/-- After the entry, from an entry state with `a`'s public data. -/
def AEnt (pc : Bool) (a t : State) : Prop := ∃ s, PreD pc s ∧ PubD a s ∧ Entered s t ∧ XP pc a s

theorem aEnt_sp {pc : Bool} {a t : State} (h : AEnt pc a t) : t.sp = fb a :=
  let ⟨_, _, p, E, _⟩ := h; by rw [E.sv.sp, fb, fb, p.sp]

/-- The private operation, from the entry to `DX`. -/
theorem priv_ct (pc : Bool) : RelCT isa (Two (AEnt pc)) (priv pc) fun _ _ => True := by
  unfold priv
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, PreD pc s ∧ PubD a s ∧ w.sp = fb s ∧
      WP isa (.block [.lsr .w .r20 .r3 0]) w (AfterPriv s))
    (two_alloc (R := fun _ _ => True) (fun a t₁ t₂ h₁ h₂ => ⟨(aEnt_sp h₁).trans (aEnt_sp h₂).symm, fun _ h => nomatch h⟩) ?_)
    fun a t ⟨s, P, p, E, x⟩ => WP.mono (privF_ok P (fun h => (x h).1) E) fun w h => ⟨s, P, p, h⟩)
    (lsr_taint fun a w₁ w₂ ⟨s₁, _, p₁, e₁, _⟩ ⟨s₂, _, p₂, e₂, _⟩ =>
      ⟨by rw [e₁, e₂, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  refine two_seq (Ψ := APriv pc) (privArgs_taint pc fun a u₁ u₂ ⟨t₁, h₁, e₁⟩ ⟨t₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, aEnt_sp h₁, aEnt_sp h₂], fun _ h => nomatch h⟩)
    (fun a u ⟨t, ⟨s, P, p, E, x⟩, e⟩ => by
      subst e; exact WP.mono (privArgsG_ok P E) fun u' A => ⟨s, P, p, A, x⟩)
    (call_ct pc)

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end


/-!
# RSAES-OAEP decryption on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data leak alike: the code between the calls by the
taint analysis (`Dc/CTBlocks`), the private operation by its constant time
(`priv_ct`), the hash functions' calls through the tables by their
contracts (`hashLabelT_ct`, MGF1's `mgfXorT_ctS`, with each table at the
same address and its functions at the same addresses: `DXT`), the branch on
the label's digest length (`byLen_ct`) and that on the public `k`
(`two_ite`); what each run satisfies between them follows from correctness. The scan's index,
the shift's count and the private operation's result differ between the
runs, but only as data.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi wp_nil
  eval_nonzero)
open VG.Proof.RsaOaep (scan_idx)

/-- `k` passed the check, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 ≤ (a.gpr .r7).toNat

theorem hk_s {D : Nat} {a s : State} (p : PubD a s) (h : HK D a) : 2 * D + 2 ≤ kk s := by
  show 2 * D + 2 ≤ (s.gpr .r7).toNat; rw [p.g .r7 (by decide)]; exact h

/-- `G`'s functions at the anchor's addresses. -/
def SymG (G : Hash) (a s : State) : Prop :=
  s.syms G.initN = a.syms G.initN ∧ s.syms G.updN = a.syms G.updN ∧ s.syms G.finN = a.syms G.finN

/-- Both tables on entry: MGF1's, `G`'s, and the label's hash function's,
`H`'s. -/
def TT (G H : Hash) (f : Fns) (s : State) : Prop :=
  TabS G f 16 (SD s) s (stackArg s 16) ∧ TabS H f 15 (SD s) s (stackArg s 15)

/-- Both tables' functions at the anchor's addresses. -/
def SymGH (G H : Hash) (a s : State) : Prop := SymG G a s ∧ SymG H a s

/-- `DX`, with both tables on entry, their functions at the anchor's
addresses, and the entry's addresses of statics. -/
def DXT (G H : Hash) (f : Fns) (a t : State) : Prop :=
  ∃ pc s m, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ Frame [kD s, scR s] s.mem m ∧
    Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t ∧ t.syms = s.syms

theorem DXT.dx {G H : Hash} {f : Fns} {a t : State} (h : DXT G H f a t) : DX a t :=
  let ⟨_, s, m, P, _, p, _, hm, b, _⟩ := h; ⟨_, s, m, P, p, hm, b⟩

theorem DXT.only {G H : Hash} {f : Fns} {a t t' : State} {rs : List Reg} (h : DXT G H f a t) (o : Only rs t t')
    (hy : t'.syms = t.syms) (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : DXT G H f a t' :=
  let ⟨_, s, m, P, T, p, y, hm, b, sy⟩ := h; ⟨_, s, m, P, T, p, y, hm, b.only (fitsM P) o hrs, hy.trans sy⟩

/-- The base state's precondition, with MGF1's table. -/
def PreXT (G : Hash) (f : Fns) (x : State) : Prop := PreX x ∧ TabS G f 16 SX x (stackArg x 16)

/-- The base state's public data, with MGF1's table's address and `G`'s
functions' addresses. -/
def PubXT (G : Hash) (a x : State) : Prop := PubX a x ∧ stackArg x 16 = stackArg a 16 ∧ SymG G a x

theorem okXT (G : Hash) (f : Fns) : OkS SX (PreXT G f) (PubXT G) := ⟨fun h => h.1, fun p => p.1.1, fun p => p.1.2⟩

theorem tabXT (G : Hash) (f : Fns) : TabA G f 16 SX (PreXT G f) (PubXT G) :=
  ⟨fun h => h.2, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2⟩

/-- What the label's hash needs of the base state: the label readable, apart
from what the hash function writes in `scratch` and from the stack. -/
def LabX (H : Hash) (x : State) : Prop :=
  (⟨stackArg x 9, (stackArg x 10).toNat⟩ : Region) ∈ x.rd ∧
    Region.Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ⟨off (SX x) oSt, H.S⟩ ∧
    Region.Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ⟨off (SX x) oW, H.W⟩ ∧
    (cR x).Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ∧ (stackArg x 10).toNat < 2 ^ 64

/-- The base state's precondition, with both tables and the label. -/
def PreXL (G H : Hash) (f : Fns) (x : State) : Prop :=
  PreXT G f x ∧ TabS H f 15 SX x (stackArg x 15) ∧ LabX H x

/-- The base state's public data, with both tables' addresses, their
functions' addresses, and the label. -/
def PubXL (G H : Hash) (a x : State) : Prop :=
  PubXT G a x ∧ stackArg x 15 = stackArg a 15 ∧ SymG H a x ∧ stackArg x 9 = stackArg a 9 ∧
    stackArg x 10 = stackArg a 10

theorem okXL (G H : Hash) (f : Fns) : OkS SX (PreXL G H f) (PubXL G H) :=
  ⟨fun h => h.1.1, fun p => p.1.1.1, fun p => p.1.1.2⟩

theorem tabXL (G H : Hash) (f : Fns) : TabA H f 15 SX (PreXL G H f) (PubXL G H) :=
  ⟨fun h => h.2.1, fun p => p.2.1, fun p => p.2.2.1.1, fun p => p.2.2.1.2.1, fun p => p.2.2.1.2.2⟩

/-- The base state of a run for the label's hash, from the decoding's. -/
theorem DXT.toL {G H : Hash} (hH : HashOK H) {f : Fns} {a t : State} (h : DXT G H f a t) :
    BT SX VX (PreXL G H f) (PubXL G H) a t := by
  obtain ⟨_, s, m, P, T, p, y, hm, b, sy⟩ := h
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  have a16 : stackArg (bx s m (rcOf (privO s))) 16 = stackArg s 16 := stackArg_bx P hm _ (by decide)
  have a15 : stackArg (bx s m (rcOf (privO s))) 15 = stackArg s 15 := stackArg_bx P hm _ (by decide)
  have a9 : stackArg (bx s m (rcOf (privO s))) 9 = stackArg s 9 := stackArg_bx P hm _ (by decide)
  have a10 : stackArg (bx s m (rcOf (privO s))) 10 = stackArg s 10 := stackArg_bx P hm _ (by decide)
  have h13 : SX (bx s m (rcOf (privO s))) = Sd s := stackArg_bx P hm _ (i := 13) (by decide)
  refine ⟨_, ⟨⟨pX, by rw [a16]; exact tabS_to P T.1 hm rfl rfl rfl (by simp only [SC, h13])⟩,
    by rw [a15]; exact tabS_toL P T.2 hm rfl rfl rfl (by simp only [SC, h13]), ?_⟩,
    ⟨⟨pubX_bx P hm p, a16.trans (p.args 16 (by decide)), y.1⟩, a15.trans (p.args 15 (by decide)), y.2,
      a9.trans (p.args 9 (by decide)), a10.trans (p.args 10 (by decide))⟩, bX, sy⟩
  show LabX H (bx s m (rcOf (privO s)))
  unfold LabX
  rw [a9, a10, h13]
  exact ⟨by show lR s ∈ s.rd; rw [P.hrd]; simp, (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)),
    (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)),
    P.kl.sub_left fun a ha => kR_sub a (cR_sub (withMem s m) a ha), BitVec.isLt _⟩

/-- `DXT` with the check passed. -/
def DK (G H : Hash) (f : Fns) (D : Nat) (a t : State) : Prop := DXT G H f a t ∧ HK D a

/-- MGF1's arguments, from the anchor. -/
def MgfD (G H : Hash) (f : Fns) (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  DXT G H f a t ∧ t.gpr .r24 = off (stackArg a 13) src ∧ t.gpr .r25 = BitVec.ofNat 64 srcLen ∧
    t.gpr .r26 = off (stackArg a 13) dst ∧ t.gpr .r27 = BitVec.ofNat 64 dstLen

theorem MgfD.toA {G H : Hash} {f : Fns} {src srcLen dst dstLen : Nat} {a t : State}
    (h : MgfD G H f src srcLen dst dstLen a t) : MgfAT SX VX (PreXT G f) (PubXT G) src srcLen dst dstLen a t := by
  obtain ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, h24, h25, h26, h27⟩ := h
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  have a16 : stackArg (bx s m (rcOf (privO s))) 16 = stackArg s 16 := stackArg_bx P hm _ (by decide)
  have h13 : SX (bx s m (rcOf (privO s))) = Sd s := stackArg_bx P hm _ (i := 13) (by decide)
  refine ⟨_, ⟨pX, ?_⟩, ⟨pubX_bx P hm p, a16.trans (p.args 16 (by decide)), y.1⟩, bX, sy, h24, h25, h26, h27⟩
  rw [a16]
  exact tabS_to P T.1 hm rfl rfl rfl (by simp only [SC, h13])

section
variable {G H : Hash} (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include cG hGh hGl hGv in
/-- `mgfXorT`, with its lengths and offsets the anchor's. -/
theorem mgf_anyD (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfD G H f (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXorT f 16) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT SX VX (PreXT G f) (PubXT G) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ctS (okXT G f) hG cG x.2 hGh hGl hGv (tabXT G f)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1.toA, h₂.1.toA⟩) fun _ _ h => h

include hGh hGl hGv in
theorem mgf_dx {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {a t : State}
    (h : MgfD G H f src srcLen dst dstLen a t) : WP isa (mgfXorT f 16) t (DXT G H f a) := by
  obtain ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, h24, h25, h26, h27⟩ := h
  exact WP.mono (mgfXorT_ok (fitsM P) hG (tabS_wm P T.1 hm) hGh hGl hGv hf b sy (h24.trans (off13 p _)) h25
    (h26.trans (off13 p _)) h27) fun _ h' => ⟨_, s, m, P, T, p, y, hm, h'.1.1, h'.2⟩

end

/-- `k` from the anchor. -/
abbrev kA (a : State) : Nat := (a.gpr .r7).toNat

theorem kA_le {a t : State} (h : DX a t) : kA a ≤ 1024 := by
  obtain ⟨_, s, m, P, p, -, -⟩ := h
  have := P.k2; rw [p.g .r7 (by decide)] at this; exact this

/-- The arguments of MGF1 of `maskedDB` into the seed. -/
theorem seed_wp {G H : Hash} {f : Fns} (hD0 : 0 < H.D) (hD64 : H.D ≤ 64) {a t : State} (h : DK G H f H.D a t) :
    WP isa (.block (seedArgs H)) t fun t' => (MgfD G H f (1 + H.D) (kA a - (H.D + 1)) 1 H.D a t' ∧
      MFit (1 + H.D) (kA a - (H.D + 1)) 1 H.D) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .r7).toNat := rfl
  obtain ⟨-, r14, r15, -, -, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (h := by omega_using [hD64, hE]) fun t₁ o₁ e₁ => wp_subi (h := by omega_using [hD64]) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega_using [hE]) fun t₃ o₃ e₃ => wp_li (by omega_using [hD64]) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega_using [hD64, hk2], by omega_using [hD64], .inr (by omega_using []), by omega_using [hD0]⟩⟩, hk⟩
  · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, r14, hE, Nat.zero_add]
  · rw [o₄.get .r25, o₃.get .r25, e₂, o₁.get .r15, r15, sub_r15 (by omega)]
  · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, r14, hE]
  · rw [e₄]

/-- The arguments of MGF1 of the seed into `maskedDB`. -/
theorem db_wp {G H : Hash} {f : Fns} (hD64 : H.D ≤ 64) {a t : State} (h : DK G H f H.D a t) :
    WP isa (.block (dbArgs H)) t fun t' => (MgfD G H f 1 H.D (1 + H.D) (kA a - (H.D + 1)) a t' ∧
      MFit 1 H.D (1 + H.D) (kA a - (H.D + 1))) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .r7).toNat := rfl
  obtain ⟨-, r14, r15, -, -, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (h := by omega_using [hE]) fun t₁ o₁ e₁ => wp_li (by omega_using [hD64]) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega_using [hD64, hE]) fun t₃ o₃ e₃ => wp_subi (h := by omega_using [hD64]) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega_using [hD64], by omega_using [hD64, hk2], .inl (by omega_using []), by omega⟩⟩, hk⟩
  · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, r14, hE]
  · rw [o₄.get .r25, o₃.get .r25, e₂]
  · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, r14, hE, Nat.zero_add]
  · rw [e₄, o₃.get .r15, o₂.get .r15, o₁.get .r15, r15, sub_r15 (by omega)]

/-- `DX` from an entry state with `a`'s public data, by the correctness
lemmas' `Base`. -/
theorem dk_wp {G H : Hash} {f : Fns} {D : Nat} {c : Prog isa} {a t : State} (h : DK G H f D a t)
    (hw : ∀ pc s m, PreD pc s → PubD a s → 2 * D + 2 ≤ kk s → Frame [kD s, scR s] s.mem m →
      Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t →
      WP isa c t fun t' => Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t') :
    WP isa c t (DK G H f D a) :=
  let ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩ := h
  WP.mono_syms (hw _ s m P p (hk_s p hk) hm b) fun _ b' y' => ⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩

/-- After the scan: the index, below the buffer's size. -/
def DI (G H : Hash) (f : Fns) (D : Nat) (a t : State) : Prop := DK G H f D a t ∧ ∃ idx < 1023, t.gpr .r25 = BitVec.ofNat 64 idx

theorem dk_pins {G H : Hash} {f : Fns} {D : Nat} {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → DK G H f D (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ [Reg.r14, .r15, .r16, .r17, .r18, .r19] := by decide) : Pins Φ rs :=
  dx_pins (fun x t hx => (h x t hx).1.dx) rs hrs

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include hH cH cG hGh hGl hGv in
theorem decMain_ct : RelCT isa (Two (DK G H f H.D)) (decMain H f) fun _ _ => True := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  unfold decMain
  -- The seed with MGF1 of `maskedDB`.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, kA a - (H.D + 1), 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfD G H f (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => seed_wp hD0 hD64 h) ?_
  refine two_seq (Ψ := DK G H f H.D) ((mgf_anyD hG cG hGh hGl hGv q₁).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `maskedDB` with MGF1 of the seed.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, kA a - (H.D + 1))
  refine two_seq (Ψ := fun a t => (MgfD G H f (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => db_wp hD64 h) ?_
  refine two_seq (Ψ := DK G H f H.D) ((mgf_anyD hG cG hGh hGl hGv q₂).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `lHash`, and `lHash'` against it.
  refine two_seq (Ψ := DK G H f H.D) ((hashLabelT_ct (vf := VX) (okXL G H f) hH cH (tabXL G H f) (rl := .r18)
      (rn := .r19)
      (L := fun x => stackArg x 9) (N := fun x => (stackArg x 10).toNat) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (fun {x t} _ b => ⟨b.vs .r18 (by decide), by
        rw [b.vs .r19 (by decide)]; show stackArg x 10 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩)
      (fun _ p => ⟨p.2.2.2.1, by rw [p.2.2.2.2]⟩) (fun P => P.2.2) (fun h => lab2_taint h)
      (fun h => lab3_taint h)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁.1.toL hH, h₂.1.toL hH⟩) fun _ _ h => h)
    (fun a t ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩ => WP.mono (hashLabelT_ok P hH (tabS_wmL P T.2 hm) b sy)
      fun t' ⟨⟨b', _⟩, y'⟩ => ⟨⟨_, s, m, P, T, p, y, hm, b', y'⟩, hk⟩) ?_
  refine two_seq (Ψ := DK G H f H.D) (accLh_taint H (dk_pins (an := id) (fun _ _ h => h) [.r14]))
    (fun a t h => dk_wp h fun _ s m P _ hk _ b => WP.mono (accLh_ok P rfl hD0 hD64 hk b) fun _ h' => h'.1) ?_
  -- The scan.
  refine two_seq (Ψ := DI G H f H.D) (scan_taint H (dk_pins (an := id) (fun _ _ h => h) [.r14, .r15]))
    (fun a t ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩ => ?_) ?_
  · have hk' := hk_s p hk
    have hk2 := P.k2
    refine WP.mono_syms (scan_ok P rfl hD64 hk' b) fun t' ⟨b', _, _, _, i'⟩ y' =>
      ⟨⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, ?_⟩
    obtain ⟨idx, he, hi⟩ := scan_idx (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) (t.gpr .r24)
      (kk s - (2 * H.D + 1))
    exact ⟨idx, by unfold kk at *; omega_using [hk2, hi], i'.trans he⟩
  -- The buffer.
  refine two_seq (Ψ := DI G H f H.D) (clearBuf_taint (dk_pins (an := id) (fun _ _ h => h.1) [.r14]))
    (fun a t ⟨⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h25⟩ => WP.mono_syms (clearBuf_ok P b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g' .r25 (by simp)).trans h25⟩) ?_
  refine two_seq (Ψ := DI G H f H.D) (copyT_taint H (dk_pins (an := id) (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t ⟨⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h25⟩ => WP.mono_syms (copyT_ok P rfl hD64 (hk_s p hk) b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g' .r25 (by simp)).trans h25⟩) ?_
  -- The shift, `ok`, `out`, the length and the result.
  refine two_seq (Ψ := DK G H f H.D) (shift_taint (dk_pins (an := id) (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t ⟨h, idx, hi, h25⟩ => dk_wp h fun _ s m P _ _ _ b => WP.mono (shift_ok P b h25 hi) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := DK G H f H.D) (okMask_taint (dk_pins (an := id) (fun _ _ h => h) []))
    (fun a t h => dk_wp h fun _ s m P _ _ _ b => WP.mono (okMask_ok P b (rcOf_le _)) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := fun a t => t.sp = fb a ∧ t.gpr .r17 = a.gpr .r5)
    (outLoop_taint (dk_pins (an := id) (fun _ _ h => h) [.r14, .r15, .r16])) (fun a t h => ?_) ?_
  · obtain ⟨-, -, -, -, r17, -, -⟩ := h.1.dx.pins
    obtain ⟨⟨_, s, m, P, -, p, -, hm, b, -⟩, -⟩ := h
    exact WP.mono (outLoop_ok P b) fun t' ⟨sv, _, g', _⟩ =>
      ⟨by rw [sv.sp, fb, fb, p.sp], (g' .r17 (by simp)).trans r17⟩
  exact decRet_taint H fun a t₁ t₂ h₁ h₂ => ⟨h₁.1.trans h₂.1.symm, fun r hr => by
    rw [List.mem_singleton.mp hr, h₁.2, h₂.2]⟩

end

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)

/-- After the entry, from an entry state with MGF1's table, `G`'s, and `a`'s
public data. -/
def AEntT (pc : Bool) (G H : Hash) (f : Fns) (a t : State) : Prop :=
  ∃ s, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ Entered s t ∧ t.syms = s.syms ∧ XP pc a s

/-- After the private operation, from such an entry state. -/
def AP (G H : Hash) (f : Fns) (a v : State) : Prop :=
  ∃ pc s, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ AfterPriv s v ∧ v.syms = s.syms

/-- After the check of `k`. -/
def AC (G H : Hash) (f : Fns) (D : Nat) (a v : State) : Prop :=
  ∃ pc s, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ AfterPriv s v ∧ v.syms = s.syms ∧
    (v.gpr .r3 != 0) = decide (kk s < 2 * D + 2)

theorem AC.dxt {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) : DXT G H f a v :=
  let ⟨_, s, P, T, p, y, A, sy, _⟩ := h; ⟨_, s, v.mem, P, T, p, y, A.mem, A.base, sy⟩

theorem AC.dx {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) : DX a v := h.dxt.dx

theorem AC.r3 {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) :
    (v.gpr .r3 != 0) = decide (kA a < 2 * D + 2) := by
  obtain ⟨_, s, _, _, p, _, _, _, r⟩ := h
  rw [r]; show decide ((s.gpr .r7).toNat < _) = _; rw [p.g .r7 (by decide)]

theorem AP.dxt {G H : Hash} {f : Fns} {a v : State} (h : AP G H f a v) : DXT G H f a v :=
  let ⟨_, s, P, T, p, y, A, sy⟩ := h; ⟨_, s, v.mem, P, T, p, y, A.mem, A.base, sy⟩

theorem AP.only {G H : Hash} {f : Fns} {a v v' : State} {rs : List Reg} (h : AP G H f a v) (o : Only rs v v')
    (y : v'.syms = v.syms) (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : AP G H f a v' :=
  let ⟨_, s, P, T, p, g, A, sy⟩ := h; ⟨_, s, P, T, p, g, A.only P o hrs, y.trans sy⟩

include hH cH hG cG hHh hHl hHv hGh hGl hGv in
theorem code_ct (pc : Bool) {f : Fns} (hl : H.D ∈ lens) :
    RelCT isa (Two fun a s => (PreD pc s ∧ TT G H f s) ∧ (PubD a s ∧ SymGH G H a s) ∧ XP pc a s) (decryptG pc f)
      fun _ _ => True := by
  have hD64 := hH.hD64
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.2.1.1.sp.trans h₂.2.1.1.sp.symm, fun _ h => nomatch h⟩) ?_
  refine two_seq (Ψ := AEntT pc G H f)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.1.1.sp,
      h₂.2.1.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨⟨P, T⟩, ⟨p, g⟩, x⟩, e⟩ => by
      subst e; exact WP.mono_syms (entry_ok P) fun t E y => ⟨s, P, T, p, g, E, y, x⟩) ?_
  refine two_seq (Ψ := AP G H f) ((priv_ct pc).mono
      (fun _ _ ⟨a, ⟨s₁, P₁, _, p₁, _, E₁, _, x₁⟩, ⟨s₂, P₂, _, p₂, _, E₂, _, x₂⟩⟩ =>
        ⟨a, ⟨s₁, P₁, p₁, E₁, x₁⟩, ⟨s₂, P₂, p₂, E₂, x₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, T, p, g, E, sy, x⟩ => WP.mono_syms (priv_ok P (fun h => (x h).1) E) fun v A y =>
      ⟨_, s, P, T, p, g, A, y.trans sy⟩) ?_
  -- The label's hash function's digest length to `r3`.
  let A₃ := fun (a v : State) => AP G H f a v ∧ v.gpr .r3 = BitVec.ofNat 64 H.D
  have hlen : RelCT isa (Two (AP G H f)) (.block (lenLoad 15)) (Two A₃) :=
    (tword_two (okXL G H f) (tabXL G H f) (Φ := fun (ac : State × Nat) t => AP G H f ac.1 t)
      (fun _ _ h => h.dxt.toL hH) (d := .r3) (.inr (.inr rfl)) (k := 6) (by decide)
      (v := fun _ => BitVec.ofNat 64 H.D) fun P _ => P.2.1.d).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁, h₂⟩)
      fun _ _ ⟨ac, ⟨t₁, h₁, o₁, z₁, e₁⟩, ⟨t₂, h₂, o₂, z₂, e₂⟩⟩ => ⟨ac.1, ⟨h₁.only o₁ z₁, e₁⟩, ⟨h₂.only o₂ z₂, e₂⟩⟩
  refine RelCT.seq hlen ?_
  -- The code for that length.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ pc s, PreD pc s ∧ PubD a s ∧ Saves s u)
    (byLen_ct (D := H.D) (Φ := A₃) (by omega_using [hD64]) (fun _ _ h => h.2)
      (fun _ _ _ h₁ h₂ => h₁.1.dxt.dx.pins.1.trans h₂.1.dxt.dx.pins.1.symm)
      (fun _ _ _ ⟨h, r3⟩ o y => ⟨h.only o y, by rw [o.get .r3]; exact r3⟩) ?_ hl lens_certs)
    fun a v ⟨⟨_, s, P, T, p, g, A, sy⟩, h3⟩ => ?_)
    (restore_taint fun a u₁ u₂ ⟨_, s₁, _, p₁, v₁⟩ ⟨_, s₂, _, p₂, v₂⟩ =>
      ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  · rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
    refine two_seq (Ψ := AC G H f H.D) (chkK_taint H (dx_pins (an := id) (fun _ _ h => h.1.dxt.dx) []))
      (fun a v ⟨⟨_, s, P, T, p, g, A, sy⟩, _⟩ => WP.mono_syms (chk_ok P hH.hD64 A) fun _ ⟨A', r⟩ y =>
        ⟨_, s, P, T, p, g, A', y.trans sy, r⟩) ?_
    refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.r3, h₂.r3])
      (decFail_taint (dx_pins (an := id) (fun _ _ h => h.1.dx) [.r15, .r16, .r17])) ?_
    refine (decMain_ct hH cH hG cG hGh hGl hGv).mono (fun _ _ ⟨a, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩ => ?_) fun _ _ h => h
    rw [eval_nonzero, h₁.r3] at c₁
    have hk : HK H.D a := by simp at c₁; omega
    exact ⟨a, ⟨h₁.dxt, hk⟩, ⟨h₂.dxt, hk⟩⟩
  · refine byLen_ok (D := H.D) (by omega_using [hD64])
      (F := fun u => AfterPriv s u ∧ u.syms = s.syms ∧ u.gpr .r3 = BitVec.ofNat 64 H.D)
      (fun _ h => h.2.2) (fun u u' ⟨A', y', r3'⟩ o y => ⟨A'.only P o, y.trans y', by rw [o.get .r3]; exact r3'⟩)
      ?_ hl (fun x hx => (lens_certs x hx).1) v ⟨A, sy, h3⟩
    intro u ⟨A', y', _⟩
    rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
    exact WP.seq (WP.mono (checks_done hH hG hHh hHl hHv hGh hGl hGv P T.1 T.2 A' y') fun v' h => WP.mono h
      fun _ d => ⟨_, s, P, p, d.1⟩)

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-!
# RSAES-OAEP decryption on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Constant time
(`code_constantTime`, from `code_ct`, for the tables of the first run, which
the public data makes the second's); a state meeting the precondition, with
both tables that of any `w` of `vs`, at `0x300000` (`dec_sat`); and
`dec_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)

open VG.Proof.MdHashTable.PPC64LE (MVar tables fns3 Coh)

theorem code_constantTime {vs : List MVar} (hc : Coh vs) :
    ConstantTime isa (decSpec (tables vs)).pre (decSpec (tables vs)).pub (decrypt (fns3 vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, hpw₁⟩ := spec_tabD h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, hsy, hiffL, hiff⟩ := pubD_of hp
  have hhL₂ := (hiffL _ hT₁).mp hhL₁
  have hh₂ := (hiff _ hT).mp hh₁
  have q₁ := hpw₁.sublist (List.sublist_append_left _ _)
  have q₂ := (spec_tabD h₂).2.2.sublist (List.sublist_append_left _ _)
  have hn := Proof.MdHashTable.PPC64LE.mem_names hw
  have hnL := Proof.MdHashTable.PPC64LE.mem_names hw₁
  have P₁ := preD_of h₁
  have P₂ := preD_of h₂
  exact code_ct w₁.l.ok w₁.l.ct w.l.ok w.l.ct w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len w.l.valid
    false w₁.l.lens_mem _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entryD hc P₁ q₁ hw hh₁, tabS_entryDL hc P₁ q₁ hw₁ hhL₁⟩, ⟨pubD_refl s₁, ⟨rfl, rfl, rfl⟩,
        ⟨rfl, rfl, rfl⟩⟩, nofun⟩,
      ⟨⟨P₂, tabS_entryD hc P₂ q₂ hw hh₂, tabS_entryDL hc P₂ q₂ hw₁ hhL₂⟩, ⟨p,
        ⟨(hsy _ hn.1).symm, (hsy _ hn.2.1).symm, (hsy _ hn.2.2.1).symm⟩,
        ⟨(hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm, (hsy _ hnL.2.2.1).symm⟩⟩, nofun⟩⟩ e₁ e₂

/-- `vg_rsa_oaep_decrypt` against its contract, for the tables of `vs`,
given a state meeting it. -/
theorem dec_verified {vs : List MVar} (hc : Coh vs) (hsat : ∃ s, (decSpec (tables vs)).pre s) :
    Verified PPC64LE.target (decrypt (fns3 vs)) (decSpec (tables vs)) :=
  ⟨code_correct hc, code_constantTime hc, hsat⟩

/-! ## A state meeting the precondition -/

/-- A state meeting decryption's contract, but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, an empty label, a
working space of 2080 words, the stack arguments at `sp + 96`, and both
tables' address `0x300000`. -/
def decSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1800 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x3000 | .r9 => 1
    | .r10 => 0x4200 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10060 then 1
    else bif Nat.beq a.toNat 0x10069 then 0x43 else bif Nat.beq a.toNat 0x10070 then 1
    else bif Nat.beq a.toNat 0x10079 then 0x44 else bif Nat.beq a.toNat 0x10080 then 1
    else bif Nat.beq a.toNat 0x10089 then 0x45 else bif Nat.beq a.toNat 0x10090 then 1
    else bif Nat.beq a.toNat 0x10099 then 0x46 else bif Nat.beq a.toNat 0x100A0 then 1
    else bif Nat.beq a.toNat 0x100A9 then 0x47 else bif Nat.beq a.toNat 0x100B9 then 0x41
    else bif Nat.beq a.toNat 0x100C0 then 64 else bif Nat.beq a.toNat 0x100CA then 0x02
    else bif Nat.beq a.toNat 0x100D0 then 0x20 else bif Nat.beq a.toNat 0x100D1 then 0x08
    else bif Nat.beq a.toNat 0x100DA then 0x30 else bif Nat.beq a.toNat 0x100E2 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10060, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List MVar} {w : MVar}

theorem stackArgAddr_dsat (j : Nat) (hj : j < 17) : (stackArgAddr decSatState j).toNat + 8 ≤ 0x300000 := by
  revert j; decide

theorem stackArg_dsat {j : Nat} {v : Addr} (hj : j < 17) (e : stackArg decSatState j = v) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) j = v :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_dsat j hj)).trans e

theorem dsat_args :
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 0 = 1 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 1 = 0x4300 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 2 = 1 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 3 = 0x4400 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 4 = 1 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 5 = 0x4500 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 6 = 1 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 7 = 0x4600 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 8 = 1 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 9 = 0x4700 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 10 = 0 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 11 = 0x4100 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 12 = 64 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 13 = 0x20000 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 14 = 2080 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 15 = 0x300000 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 16 = 0x300000 :=
  ⟨stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide)⟩

/-- A state meeting the contract, with both tables that of `w`, at
`0x300000`. -/
theorem dec_sat (hw : w ∈ vs) (hl : (Proof.MdHashTable.PPC64LE.names vs).length < 2 ^ 32) :
    ∃ s, (decSpec (tables vs)).pre s := by
  refine ⟨Proof.MdHashTable.PPC64LE.withTable decSatState vs w, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ :=
    dsat_args (vs := vs) (w := w)
  have e : stackArgAddr (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 0 = 0x10060 :=
    show stackArgAddr decSatState 0 = _ by decide
  have e3792 : stackBytes = 3791 + 1 := rfl
  unfold decSpec
  rw [e3792]
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_seventeen, List.append_eq, List.range, List.range.loop]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    a13, a14, a15, a16, e]
  sig_and_intros
  all_goals first
    | exact ⟨Proof.MdHashTable.PPC64LE.tableOf w, List.mem_map_of_mem hw, Proof.MdHashTable.PPC64LE.held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.HashTable.symsOf_distinct2 hl
    | (unfold Spec.Rsa.lenValid; decide)
    | (unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords; decide)

end

end VG.Proof.RsaOaep.PPC64LE.Dec
