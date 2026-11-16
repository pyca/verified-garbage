module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Qinv
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Crt
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.NFin
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Out
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Ctx
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.RsaKeyGen.KeyOp
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Lcm
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DPart
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Small
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Entry
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTSmall
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTTail
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTFront
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTOut
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Key
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.AArch64.Target

/-! ### `RsaKeyGen.AArch64.Key.Code`, which only this module used -/

section

/-! ### `RsaKeyGen.AArch64.Key.Res`, which only this module used -/

section

/-! ### `RsaKeyGen.AArch64.Key.Tail`, which only this module used -/

section

/-!
# An RSA key from its primes on AArch64: the key

`keyPart`, once `d` is not too small or does not exist: `qInv`, `dP`, `dQ`,
`n`, the final mask, the stores and the status (`keyPart_k`); and the zeros
and the status 2 otherwise (`zerosPart_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- The stores. -/
def storeL (I : KIn) : List St :=
  [⟨aQt, kNo, kNl, I.pN, 2 * I.pl⟩, ⟨aDd, kDo, kNl, I.pD, 2 * I.pl⟩, ⟨aPa, kPp, kPl, I.pP, I.pl⟩,
    ⟨aQa, kQp, kPl, I.pQ, I.pl⟩, ⟨aX₁, kDp, kPl, I.pDp, I.pl⟩, ⟨aV, kDq, kPl, I.pDq, I.pl⟩,
    ⟨aX₂, kQi, kPl, I.pQi, I.pl⟩]

theorem storeL_outs (I : KIn) : (storeL I).map (fun e => (e.out, e.len)) = outsL I := rfl

theorem storeL_pairwise {I : KIn} (O : KOuts I) :
    (storeL I).Pairwise fun a b => Apart a.out a.len b.out b.len := by
  have := O.apart
  rw [← storeL_outs, List.pairwise_map] at this
  exact this

theorem st_ok {I : KIn} {s₀ t : State} (h : KS I s₀ t) (O : KOuts I) {j p l : Nat} {out : Addr}
    {len : Nat} (hj : j < 16) (hp : p < 32) (hl : l < 32) (hpv : word t.mem I.B (8 * p) = out)
    (hlv : word t.mem I.B (8 * l) = BitVec.ofNat 64 len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * I.W)
    (ho : (out, len) ∈ outsL I) : (⟨j, p, l, out, len⟩ : St).Ok t I.B I.Z I.W :=
  ⟨hj, hp, hl, hpv, hlv, hl1, hlw, fun i hi => by rw [h.wr]; exact O.wr _ ho i hi, O.sep _ ho⟩

theorem storeL_ok {I : KIn} {s₀ t : State} (h : KS I s₀ t) (L : KLens I) (O : KOuts I) :
    ∀ e ∈ storeL I, e.Ok t I.B I.Z I.W := by
  have hW := L.W
  have hpl := L.pl1
  have h8 := L.pl8
  intro e he
  simp only [storeL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.no h.args.nl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dd h.args.nl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.pp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.qp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dq h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.qi h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])

theorem outputs_eq (I : KIn) : outputs = storesK (storeL I) ++ ([.block retOk] : List (Prog isa)) := rfl

theorem zeros_eq (I : KIn) (st : Nat) :
    zeros st = seqs (zerosK (storeL I) ++ ([.block [movi .x0 st]] : List (Prog isa))) := rfl

theorem keyPart_eq (I : KIn) : keyPart = seqs (qinvPart ++ (crtPart ++ (nPart ++
    (([.block finalMask] : List (Prog isa)) ++ (storesK (storeL I) ++ ([.block retOk] : List (Prog isa))))))) := by
  rw [keyPart, ← outputs_eq I]; simp only [List.append_assoc]

/-- A number below `2^(64 v)` read from `v ≤ W` words. -/
theorem wv_of_av {I : KIn} {m : Mem} {j v x : Nat} (hv : v ≤ I.W) (h : av I m j = x) (hx : x < 2 ^ (64 * v)) :
    wv m I.B (slot I.W j) v = x := by
  rw [← h]; exact wv_low_of_lt hv (by rw [show wv m I.B (slot I.W j) I.W = av I m j from rfl, h]; exact hx)

/-- Two states that keep the registers of one before both. -/
theorem keep_of_common {rs : List Reg} {s₀ s t : State} (a : Keep rs s₀ s) (b : Keep rs s₀ t) : Keep rs s t :=
  ⟨fun r hr => (b.gpr r hr).trans (a.gpr r hr).symm, b.rd.trans a.rd.symm, b.wr.trans a.wr.symm,
    b.sp.trans a.sp.symm, fun r hr => (b.vcs r hr).trans (a.vcs r hr).symm⟩

/-- What `keyPart` leaves, from `KFront` and `kOk` the mask of `ok`. -/
def TailPost (I : KIn) (s t : State) (ok : Bool) : Prop :=
  ∃ x : Nat, ((qMod I.P : Nat) : Int) ∣ (x : Int) * I.Q - Nat.gcd I.Q (qMod I.P) ∧ x < qMod I.P ∧
    (let c := finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok)
     t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧
     Spec.Rsa.bytesAt t.mem I.pN (2 * I.pl) = Spec.Rsa.i2osp (if c then I.P * I.Q else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pD (2 * I.pl) = Spec.Rsa.i2osp (if c then av I s.mem aDd else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pP I.pl = Spec.Rsa.i2osp (if c then I.P else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQ I.pl = Spec.Rsa.i2osp (if c then I.Q else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDp I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.P - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDq I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.Q - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQi I.pl = Spec.Rsa.i2osp (if c then x else 0) I.pl) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    Keep kRegs s t

/-- `keyPart`. -/
theorem keyPart_k [VG.Proof.Rsa.AArch64.InvLaw] {I : KIn} {s₀ s : State} (h : KFront I s₀ s) (L : KLens I) (O : KOuts I) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa keyPart s (fun t => TailPost I s t ok) := by
  have hk := h.ks
  have hZ := hk.hZ
  have hW := L.W
  have hPw := L.P_lt
  have hQw := L.Q_lt
  rw [keyPart_eq I]
  -- `qInv`.
  refine wp_seqs_append (by simp [qinvPart]) (by simp [crtPart, divisorOf]) (WP.mono (qinvPart_k hk L h.vP h.vQ hPw hQw hok)
    fun s₁ ⟨h₁, f₁, ok₁, hdv₁, hx₁⟩ => ?_)
  generalize hx : av I s₁.mem aX₂ = x at hdv₁ hx₁
  obtain hokQ : csQ.all Rc.ok = true := by decide
  -- `dP`, `dQ`.
  refine wp_seqs_append (by simp [crtPart, divisorOf]) (by simp [nPart]) (WP.mono (crtPart_k h₁
    (d := av I s.mem aDd) (a := I.P - 1) (b := I.Q - 1) (by rw [f₁.av hokQ (by decide) (by decide) hZ])
    (by rw [f₁.av hokQ (by decide) (by decide) hZ, h.vPm]) (by rw [f₁.av hokQ (by decide) (by decide) hZ, h.vQm]))
    fun s₂ ⟨h₂, f₂, dP₂, dQ₂⟩ => ?_)
  obtain hokC : csC.all Rc.ok = true := by decide
  -- `n`.
  refine wp_seqs_append (by simp [nPart, mulTo]) (by simp) (WP.mono (nPart_k h₂ hW
    (by rw [f₂.av hokC (by decide) (by decide) hZ, f₁.av hokQ (by decide) (by decide) hZ]; exact h.vP)
    (by rw [f₂.av hokC (by decide) (by decide) hZ, f₁.av hokQ (by decide) (by decide) hZ]; exact h.vQ) hPw hQw)
    fun s₃ ⟨h₃, f₃, n₃⟩ => ?_)
  obtain hn : I.P * I.Q < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega_using [], Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hPw (by omega_using [hQw]) (Nat.two_pow_pos _)
  obtain hokN : [Rc.arr aQt].all Rc.ok = true := by decide
  obtain vN₃ : av I s₃.mem aQt = I.P * I.Q := av_of_full n₃ hn
  obtain vP₃ : av I s₃.mem aPa = I.P := by
    rw [f₃.av hokN (by decide) (by decide) hZ, f₂.av hokC (by decide) (by decide) hZ,
      f₁.av hokQ (by decide) (by decide) hZ, h.vP]
  obtain vQ₃ : av I s₃.mem aQa = I.Q := by
    rw [f₃.av hokN (by decide) (by decide) hZ, f₂.av hokC (by decide) (by decide) hZ,
      f₁.av hokQ (by decide) (by decide) hZ, h.vQ]
  obtain ev₃ : word s₃.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₃.word hokN (by decide) (by decide), f₂.word hokC (by decide) (by decide),
      f₁.word hokQ (by decide) (by decide), h.ev]
  obtain ok₃ : word s₃.mem I.B (8 * kOk) = mask (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok) := by
    rw [f₃.word hokN (by decide) (by decide), f₂.word hokC (by decide) (by decide), ok₁]
  -- The final mask.
  refine wp_seqs_append (by simp) (by simp [storesK, storeL, storeA]) ?_
  simp only [seqs]
  refine WP.mono (finalMask_k h₃ vN₃ vP₃ vQ₃ L.E_lt ev₃ ok₃) fun s₄ ⟨h₄, f₄, ok₄⟩ => ?_
  generalize hc : finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok) = cv at ok₄
  obtain hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  obtain v4 : ∀ j, j < 16 → Rc.arr j ∉ [Rc.arr aQt] → Rc.arr j ∉ csC → Rc.arr j ∉ csQ →
      av I s₄.mem j = av I s.mem j := fun j hj h1 h2 h3 => by
    rw [f₄.av hokO hj (by simp) hZ, f₃.av hokN hj h1 hZ, f₂.av hokC hj h2 hZ, f₁.av hokQ hj h3 hZ]
  -- The stores and the status.
  refine stores_ok (Q := fun t => TailPost I s t ok) (storeL I) _ s₄ (by simp) h₄.ws ok₄ (storeL_ok h₄ L O)
    (storeL_pairwise O) fun t ht ft bt xt kt => ?_
  simp only [seqs]
  refine WP.mono (keyExit_ok ht (c := cv) (by rw [frm_word ft ht.h256 (by decide)]; exact ok₄))
    fun u ⟨⟨hax, hmu⟩, ku⟩ => ?_
  obtain b := fun e he => (bt e he)
  simp only [storeL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at b
  obtain ⟨bN, bD, bP, bQ, bDp, bDq, bQi⟩ := b
  obtain hlen : (I.pl + 7) / 8 = I.pl / 8 := by have := L.pl8; omega_using [this]
  obtain hlen2 : (2 * I.pl + 7) / 8 = I.W := by have := L.pl8; simp only [KIn.W]; omega_using [this]
  obtain hv : I.pl / 8 ≤ I.W := by omega_using [hlen2]
  obtain hdvw : ∀ a, a ≤ I.P → dv a < 2 ^ (64 * (I.pl / 8)) := fun a ha => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := L.pl1; omega_using [this])
    · omega_using [hPw, ha]
  obtain hdvwq : ∀ a, a ≤ I.Q → dv a < 2 ^ (64 * (I.pl / 8)) := fun a ha => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := L.pl1; omega_using [this])
    · omega_using [hQw, ha]
  obtain hdv0 : ∀ a, 0 < dv a := fun a => by unfold dv; split <;> omega_arith
  obtain hqm : qMod I.P < 2 ^ (64 * (I.pl / 8)) := by
    unfold qMod; split
    · exact hPw
    · exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 2 ≤ 64 * (I.pl / 8) by
        have := L.pl1; omega_using [this]))
  obtain iv : ∀ {len v : Nat} {o : Addr} {w' : Nat},
      (List.range len).map (fun i => t.mem (o + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if cv then w' else 0) len → w' = v →
      Spec.Rsa.bytesAt u.mem o len = Spec.Rsa.i2osp (if cv = true then v else 0) len := fun hb hw => by
    simp only [Spec.Rsa.bytesAt]; rw [hmu, hb, hw]
  refine ⟨x, hdv₁, hx₁, ?_, fun y hy hny => ?_, ?_⟩
  · dsimp only
    rw [hc]
    refine ⟨hax, iv bN ?_, iv bD ?_, iv bP ?_, iv bQ ?_, iv bDp ?_, iv bDq ?_, iv bQi ?_⟩
    · rw [hlen2]; show av I s₄.mem aQt = _; rw [f₄.av hokO (by decide) (by decide) hZ, vN₃]
    · rw [hlen2]; exact v4 aDd (by decide) (by decide) (by decide) (by decide)
    · rw [hlen]; exact wv_of_av hv (v4 aPa (by decide) (by decide) (by decide) (by decide) |>.trans h.vP) hPw
    · rw [hlen]; exact wv_of_av hv (v4 aQa (by decide) (by decide) (by decide) (by decide) |>.trans h.vQ) hQw
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ, dP₂])
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (hdv0 _)) (Nat.le_of_lt (hdvw _ (by omega_using []))))
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ, dQ₂])
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (hdv0 _)) (Nat.le_of_lt (hdvwq _ (by omega_using []))))
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ,
        f₂.av hokC (by decide) (by decide) hZ, hx]) (by omega_using [hx₁, hqm])
  · have hy' : ∀ e ∈ storeL I, ∀ i < e.len, y ≠ e.out + BitVec.ofNat 64 i := fun e he i hi =>
      hny (e.out, e.len) (by rw [← storeL_outs]; exact List.mem_map_of_mem he) i hi
    rw [hmu, xt y hy', h₄.inScr y hy, hk.inScr y hy]
  · exact (((keep_of_common hk.keep h₄.keep).trans kt).trans ku).mono (by decide)

/-- What `zeros 2` leaves. -/
def ZerosPost (I : KIn) (s t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 2 ∧ (∀ o ∈ outsL I, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    Keep kRegs s t

/-- `zeros 2`: zeros to the outputs, and the status 2. -/
theorem zerosPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (L : KLens I) (O : KOuts I) :
    WP isa (zeros 2) s (ZerosPost I s) := by
  rw [zeros_eq I]
  refine zeros_ok (storeL I) _ s (by simp) h.ws (storeL_ok h L O) (storeL_pairwise O)
    fun t ht ft zt xt kt => ?_
  simp only [seqs]
  refine WP.mono (WP.keep [.x0] (Q := fun u => u.gpr .x0 = BitVec.ofNat 64 2 ∧ u.mem = t.mem) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun u ⟨⟨hax, hmu⟩, ku⟩ =>
      ⟨hax, fun o ho => ?_, fun y hy hny => ?_, (kt.trans ku).mono (by decide)⟩
  · rw [← storeL_outs] at ho
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    refine List.eq_replicate_iff.mpr ⟨by simp [Spec.Rsa.bytesAt], fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    rw [hmu]; exact zt e he i (List.mem_range.mp hi)
  · have hy' : ∀ e ∈ storeL I, ∀ i < e.len, y ≠ e.out + BitVec.ofNat 64 i := fun e he i hi =>
      hny (e.out, e.len) (by rw [← storeL_outs]; exact List.mem_map_of_mem he) i hi
    rw [hmu, xt y hy']

end VG.Proof.RsaKeyGen.AArch64.Key

end

end


/-!
# An RSA key from its primes on AArch64: the results, against `keyOp`

What the zeros (`outsRes_zeros`) and `keyPart` (`outsRes_tail`) leave is
`keyOp`'s status and outputs.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)
open VG.Spec.RsaKeyGen (keyFromPrimes)
open VG.Proof.RsaKeyGen (keyOp keyStatus)

/-- The status and the outputs `keyOp` gives. -/
def OutsRes (I : KIn) (m : Mem) (x0 : BitVec 64) : Prop :=
  (x0.setWidth 32).toNat = Proof.RsaKeyGen.keyStatus (Proof.RsaKeyGen.keyOp I.pl I.eb I.pb I.qb) ∧
    match Proof.RsaKeyGen.keyOp I.pl I.eb I.pb I.qb with
    | .inl (.ok ys) => (outsL I).map (fun o => Spec.Rsa.bytesAt m o.1 o.2) = ys
    | _ => ∀ o ∈ outsL I, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0

theorem keyOp_inr_k {pl : Nat} {eB pB qB : List Byte}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) = .inr ()) :
    keyOp pl eB pB qB = .inr () := by
  unfold keyOp; rw [h]

theorem keyOp_error_k {pl : Nat} {eB pB qB : List Byte} {f : Spec.RsaKeyGen.Failure}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.error f)) :
    keyOp pl eB pB qB = .inl (.error f) := by
  unfold keyOp; rw [h]

theorem keyOp_ok_k {pl : Nat} {eB pB qB : List Byte} {k : Spec.RsaKeyGen.Key}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.ok k)) :
    keyOp pl eB pB qB = .inl (.ok [Spec.Rsa.i2osp k.n (2 * pl), Spec.Rsa.i2osp k.d (2 * pl),
      Spec.Rsa.i2osp k.p pl, Spec.Rsa.i2osp k.q pl, Spec.Rsa.i2osp k.dP pl,
      Spec.Rsa.i2osp k.dQ pl, Spec.Rsa.i2osp k.qInv pl]) := by
  unfold keyOp; rw [h]

theorem setWidth32_k (n : Nat) (h : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [h]),
    Nat.mod_eq_of_lt h]

/-- The zeros and the status 2, for `d ≤ 2^(8 pl)`. -/
theorem outsRes_zeros {I : KIn} {s t : State} {d : Nat}
    (hd : Spec.Rsa.inverse I.E I.L = some d) (hsm : d ≤ 2 ^ (8 * I.pl)) (Z : ZerosPost I s t) :
    OutsRes I t.mem (t.gpr .x0) := by
  obtain hr : keyFromPrimes (16 * I.pl) I.E I.P₀ I.Q₀ = .inr () := by
    unfold keyFromPrimes
    obtain hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
      by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
    rw [hswap]
    dsimp only
    rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, hd, show 16 * I.pl / 2 = 8 * I.pl by omega_using []]
    dsimp only
    rw [ite_eq_left hsm]
  rw [OutsRes, keyOp_inr_k hr, Z.1]
  exact ⟨by decide, Z.2.1⟩

theorem i2osp_zero_k (k : Nat) : Spec.Rsa.i2osp 0 k = List.replicate k 0 := by
  simp [Spec.Rsa.i2osp, List.map_const']

/-- The outputs and the status of `keyPart`, for `d > 2^(8 pl)` or no `d`. -/
theorem outsRes_tail {I : KIn} {s t : State} (L : KLens I) {ok : Bool}
    (hok : (∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true)
    (hdd : ∀ d, Spec.Rsa.inverse I.E I.L = some d → av I s.mem aDd = d)
    (hb : (decide (av I s.mem aDd ≤ 2 ^ (8 * I.pl)) && ok) = false) (T : TailPost I s t ok) :
    OutsRes I t.mem (t.gpr .x0) := by
  obtain ⟨x, hx, hxl, ⟨hax, hN, hD, hP, hQ, hDp, hDq, hQi⟩, -⟩ := T
  obtain hk := keyFromPrimes_code (x := x) L.pl1 L.pl2 (lt_of_os2ip_len L.pbl) (lt_of_os2ip_len L.qbl) L.E_lt hx hxl
  obtain hW : 64 * I.W - 1 = 16 * I.pl - 1 := by rw [L.W]; have := L.pl8; omega_using [this]
  simp only [finalOk, hW] at hax hN hD hP hQ hDp hDq hQi
  obtain hstat : ∀ c : Bool, ((BitVec.ofNat 64 c.toNat).setWidth 32).toNat = c.toNat := fun c =>
    setWidth32_k _ (by cases c <;> decide)
  rcases hi : Spec.Rsa.inverse I.E I.L with _ | d
  · have hok' : ok = false := by
      cases ok
      · rfl
      · obtain ⟨d, hd⟩ := hok.mpr rfl; rw [hi] at hd; cases hd
    subst hok'
    simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, i2osp_zero_k] at hax hN hD hP
    simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, i2osp_zero_k] at hQ hDp hDq hQi
    simp only [KIn.L] at hi hk
    rw [hi] at hk
    rw [OutsRes, keyOp_error_k hk, hax, hstat]
    refine ⟨rfl, ?_⟩
    simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
  · have hok' : ok = true := hok.mp ⟨d, hi⟩
    subst hok'
    obtain hd := hdd d hi
    rw [hd, Bool.and_true, decide_eq_false_iff_not] at hb
    obtain hd2 : 2 ≤ d := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ 8 * I.pl by have := L.pl1; omega_using [this])
      omega_using [hb, this]
    obtain hqp : I.Q ≤ I.P := by simp only [KIn.P, KIn.Q]; split <;> omega_arith
    obtain ⟨hP3, hQ2, -⟩ := primes_of_inverse hqp hi hd2
    obtain hdvP : dv (I.P - 1) = I.P - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega_using [hP3]
    obtain hdvQ : dv (I.Q - 1) = I.Q - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega_using [hQ2]
    simp only [Bool.and_true, KIn.L] at hax hN hD hP hQ hDp hDq hQi hi hk
    rw [hi] at hk
    simp only [ite_eq_right_iff.mpr (fun h => absurd h hb)] at hk
    simp only [hd, hdvP, hdvQ] at hD hDp hDq
    generalize hc : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qMod I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c
      at hax hN hD hP hQ hDp hDq hQi
    have hc' : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qModP I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c := hc
    rw [hc'] at hk
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at hk
      rw [OutsRes, keyOp_error_k hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      simp only [Bool.false_eq_true, ↓reduceIte, i2osp_zero_k] at hN hD hP hQ hDp hDq hQi
      exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
    · simp only [↓reduceIte] at hk hN hD hP hQ hDp hDq hQi
      rw [OutsRes, keyOp_ok_k hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.map_cons, List.map_nil, hN, hD, hP, hQ, hDp, hDq, hQi]

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.Main`, which only this module used -/

section

/-!
# An RSA key from its primes on AArch64: from the primes to `smallMask`

`front2_k`: after `p − 1` and `q − 1` (`KPrimes`), `L = lcm(p − 1, q − 1)`,
`d` and `x15` the mask of `d` too small (`KFront`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- From `KPrimes` to `KFront`: `lcmPart`, `dPart` and `smallMask`. -/
theorem front2_k [VG.Proof.Rsa.AArch64.InvLaw] {I : KIn} {s₀ s : State} (h : KPrimes I s₀ s) (L : KLens I) :
    WP isa (seqs (lcmPart ++ ([dPart] ++ smallMask))) s (KFront I s₀) := by
  have hk := h.ks
  have hZ := hk.hZ
  have hW := L.W
  obtain hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega_using [this]
  -- `L`.
  refine wp_seqs_append (by simp [lcmPart, phi, mulTo]) (by simp) (WP.mono (lcm_k hk hW h.vPm h.vQm
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) L.P_lt) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) L.Q_lt))
    fun s₅ ⟨h₅, f₅, vL₅⟩ => ?_)
  obtain hokL : csL.all Rc.ok = true := by decide
  obtain ev₅ : word s₅.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₅.word hokL (by decide) (by decide), h.ev]
  -- `d`.
  refine wp_seqs_append (a := [dPart]) (by simp) (by simp [smallMask, constA]) ?_
  refine WP.mono (dPart_k h₅ L.E_lt ev₅ vL₅ L.L_lt) fun s₆ ⟨h₆, f₆, d₆⟩ => ?_
  obtain ⟨ok, ok₆, iff₆, dd₆⟩ := d₆
  -- `x15`.
  refine WP.mono (smallMask_k h₆ hW ok₆) fun t ⟨ht, f₇, x15₇⟩ => ?_
  obtain hokD : csD.all Rc.ok = true := by decide
  obtain hok7 : [Rc.arr aC].all Rc.ok = true := by decide
  obtain pres : ∀ j, j < 16 → Rc.arr j ∉ csD → Rc.arr j ∉ [Rc.arr aC] → Rc.arr j ∉ csL →
      av I t.mem j = av I s.mem j := fun j hj h1 h2 h3 => by
    rw [f₇.av hok7 hj h2 hZ, f₆.av hokD hj h1 hZ, f₅.av hokL hj h3 hZ]
  obtain okt : word t.mem I.B (8 * kOk) = mask ok := by rw [f₇.word hok7 (by decide) (by decide), ok₆]
  obtain hD : av I t.mem aDd = av I s₆.mem aDd := f₇.av hok7 (by decide) (by decide) hZ
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ⟨ok, okt, iff₆, fun d hd => by rw [hD]; exact dd₆ d hd⟩,
    ⟨ok, okt, iff₆, by rw [x15₇, hD, hw8]⟩⟩
  · rw [pres aPa (by decide) (by decide) (by decide) (by decide), h.vP]
  · rw [pres aQa (by decide) (by decide) (by decide) (by decide), h.vQ]
  · rw [pres aPm (by decide) (by decide) (by decide) (by decide), h.vPm]
  · rw [pres aQm (by decide) (by decide) (by decide) (by decide), h.vQm]
  · rw [f₇.word hok7 (by decide) (by decide), f₆.word hokD (by decide) (by decide), ev₅]

end VG.Proof.RsaKeyGen.AArch64.Key

end

end


/-!
# An RSA key from its primes on AArch64: correctness

`code`, from a state `keyA` allows, ends as `keyOp` (`keyCode_wp`,
`keyCode_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

theorem code_eq : code = seqs (([.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)] : List (Prog isa)) ++
    ((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ (([.block [sth .x3 kEv]] : List (Prog isa)) ++
      (order ++ (decTo aPm aPa ++ decTo aQm aQa)))))) ++
    ((lcmPart ++ ([dPart] ++ smallMask)) ++ ([.ite (.nonzero .x .x15) (zeros 2) keyPart] : List (Prog isa))))) := by
  simp only [code, List.append_assoc]

/-- The postcondition, from the results against `keyOp`. -/
theorem keyPost_of {s t : State} (c : KCtx s) (R : OutsRes (keyIn s) t.mem (t.gpr .x0)) : keyPost s t := by
  obtain ho : keyOuts s = outsL (keyIn s) := by simp only [keyOuts, outsL, keyIn, c.x1]
  unfold keyPost keyRes
  rw [ho]
  exact R

theorem mask_bne_k (b : Bool) : (mask b != 0) = b := by cases b <;> decide

/-- `code` computes `keyOp`. -/
theorem keyCode_wp [VG.Proof.Rsa.AArch64.InvLaw] (s : State) (h : keyPre s) : WP isa code s fun t => abiPreserved s t ∧ keyPost s t := by
  obtain c := keyCtx_of h
  rw [code_eq]
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (keyStart_k c) fun t₁ k₁ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [lcmPart, phi, mulTo])
    (WP.mono (front_k k₁ c.L) fun t₂ P => ?_)
  refine wp_seqs_append (by simp [lcmPart, phi, mulTo]) (by simp) (WP.mono (front2_k P.1 c.L) fun t₃ F => ?_)
  obtain ⟨ok, hok, hiff, hx15⟩ := F.x15
  obtain ⟨ok', hok', -, hdd⟩ := F.d
  obtain hoo : ok' = ok := by
    rw [hok] at hok'
    cases ok <;> cases ok' <;> first | rfl | exact absurd hok' (by decide)
  subst hoo
  refine WP.ite (decide (av (keyIn s) t₃.mem aDd ≤ 2 ^ (8 * (keyIn s).pl)) && ok')
    (by rw [VG.Proof.MlKem.AArch64.eval_nonzero, hx15, mask_bne_k]) (fun hb => ?_) (fun hb => ?_)
  · -- `d ≤ 2^(8 pl)`: zeros, the status 2.
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨d, hd⟩ := hiff.mpr hb.2
    obtain hsm := hdd d hd ▸ hb.1
    exact WP.mono (zerosPart_k F.ks c.L c.O) fun t Z =>
      ⟨abiPreserved_of_keep ((F.ks.keep.trans Z.2.2.2).mono (by decide)), keyPost_of c (outsRes_zeros hd hsm Z)⟩
  · refine WP.mono (keyPart_k F c.L c.O hok) fun t T => ?_
    obtain R := outsRes_tail c.L hiff hdd hb T
    obtain ⟨_, _, _, _, _, kt⟩ := T
    exact ⟨abiPreserved_of_keep ((F.ks.keep.trans kt).mono (by decide)), keyPost_of c R⟩

/-- `vg_rsa_keygen_key`. -/
theorem keyCode_correct [VG.Proof.Rsa.AArch64.InvLaw] (s : State) (h : keyA.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ keyA.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := keyCode_wp s h
  exact ⟨t, s', he, hg, hp⟩

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.CTCode`, which only this module used -/

section

/-!
# `vg_rsa_keygen_key` on AArch64: constant time

The pieces leak the same in runs with the same public data (`KP`): the
front, the lcm, `d` (whose branches depend on `e` alone), the mask of a
small `d`, and the branch on it (`branch_ct`: status 2, the leak's), to the
zeros or to the key and its outputs (`keyCode_ct`); hence the contract's
`ConstantTime` (`keyCode_constantTime`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

theorem code_ct_eq : code = seqs (([.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)] : List (Prog isa)) ++
    (frontL ++ (lcmPart ++ (([dPart] : List (Prog isa)) ++ (smallMask ++
      ([.ite (.nonzero .x .x15) (zeros 2) keyPart] : List (Prog isa))))))) := by
  simp only [code, frontL, List.append_assoc]

/-- The branch on a small `d`, status 2 (the leak's). -/
theorem branch_ct [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG FF)) (.ite (.nonzero .x .x15) (zeros 2) keyPart) fun _ _ => True :=
  kg_ite (kg_nonzero_eq (g := fun p => mask (decide (p.st = 2))) fun _ _ hf => hf.x15)
    (zeros2_ct.mono (fun _ _ ⟨p, h₁, h₂, hsp⟩ =>
      ⟨p, EG.of_kg (h₁.imp fun _ _ => trivial), EG.of_kg (h₂.imp fun _ _ => trivial), hsp⟩)
      fun _ _ h => h)
    (keyPart_ct.mono (fun _ _ h => two_kg (fun _ _ ⟨⟨hp, _, ok, hok, _⟩, _⟩ => ⟨hp, ok, hok⟩) h) fun _ _ h => h)

/-- `vg_rsa_keygen_key` leaks the same in runs with the same public data. -/
theorem keyCode_ct [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two KRel) code fun _ _ => True := by
  rw [code_ct_eq]
  refine rs_app (by simp) (by simp [frontL, loadA]) Key.start_ct ?_
  refine rs_app (by simp [frontL, loadA]) (by simp [lcmPart, phi, mulTo]) front_ct ?_
  refine rs_app (by simp [lcmPart, phi, mulTo]) (by simp) lcmPart_ct ?_
  refine rs_app (by simp) (by simp [smallMask, constA]) dPart_ct ?_
  exact rs_app (by simp [smallMask, constA]) (by simp) smallMask_ct branch_ct

/-- `vg_rsa_keygen_key` is constant time but for the lengths, `e`, and
whether `d` is too small. -/
theorem keyCode_constantTime [VG.Proof.Rsa.AArch64.InvLaw] : ConstantTime isa keyA.pre keyA.pub code := keyCT_of keyCode_ct

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.Implies`, which only this module used -/

section

/-!
# An RSA key from its primes on AArch64: the shared contract implies `keyA`
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-- A state meeting the precondition: 32-byte primes, a one-byte `e`, the
stack arguments at `0x9000`. -/
def keySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 32 | .x6 => 0x4000
    | .x7 => 32 | _ => 0
  sp := 0x9000
  mem a := if a = 0x9048 then 0x20
    else if a = 0x9001 then 0x50 else if a = 0x9008 then 0x20 else if a = 0x9011 then 0x60 else
    if a = 0x9018 then 0x20 else if a = 0x9021 then 0x70 else if a = 0x9028 then 0x20 else
    if a = 0x9031 then 0x80 else if a = 0x9038 then 0x01 else if a = 0x9042 then 0x01 else
    if a = 0x9049 then 0x04 else 0
  rd := [⟨0x8000, 1⟩, ⟨0x9000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x5000, 32⟩, ⟨0x6000, 32⟩, ⟨0x7000, 32⟩,
    ⟨0x10000, 8448⟩]

theorem key_implies : keyA.Implies (Proof.RsaKeyGen.keyContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre,
      stackArgs_ten, List.append_eq] at h
    sig_pre [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre,
      stackArgs_ten, List.append_eq] at h
    sig_split h
    sig_reduce [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre,
      stackArgs_ten, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    intro s s' _ h
    sig_post [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_ten, List.append_eq]
    sig_reduce [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_ten, List.append_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    revert h2
    simp only [arg]
    generalize Proof.RsaKeyGen.keyOp _ _ _ _ = r
    rcases r with (f | ys) | u <;> first | exact id | simp
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPub,
      keyLeak, keyRes, stackArgs_ten, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, hsp, fun i hi => ?_, hl⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega_using [hi]) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact a0
      · exact a1
      · exact a2
      · exact a3
      · exact a4
      · exact a5
      · exact a6
      · exact a7
      · exact a8
      · exact a9
  sat := by sig_implies_sat [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs,
    keyA, keyPre, stackArgs_ten, List.append_eq] [keySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using keySat

end VG.Proof.RsaKeyGen.AArch64.Key

end

end


/-!
# `vg_rsa_keygen_key` on AArch64: verified against the shared contract

With correctness (`keyCode_correct`), constant time (`keyCode_constantTime`)
and the shared contract's implication (`key_implies`), `code` is verified
(`key_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64

instance keyProof [VG.Proof.Rsa.AArch64.InvLaw] : KeyProof := ⟨keyCode_correct, keyCode_constantTime⟩

/-- `vg_rsa_keygen_key`. -/
theorem key_verified [VG.Proof.Rsa.AArch64.InvLaw] :
    Verified target VG.Impl.RsaKeyGen.AArch64.Key.code (Proof.RsaKeyGen.keyContract abi) :=
  Verified.of_correct keyCode_correct keyCode_constantTime key_implies

end VG.Proof.RsaKeyGen.AArch64.Key
