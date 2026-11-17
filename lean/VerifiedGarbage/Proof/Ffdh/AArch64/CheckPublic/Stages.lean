module

public import VerifiedGarbage.Proof.Ffdh.AArch64.SetupCT
public import VerifiedGarbage.Proof.Ffdh.AArch64.ChecksCT
public import VerifiedGarbage.Proof.Ffdh.AArch64.PowCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import VerifiedGarbage.Proof.Ffdh.AArch64.Front
public import VerifiedGarbage.Proof.Ffdh.AArch64.Scan
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Ffdh.AArch64.CheckPublic.Correct`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.CheckPublic.Contract`, which this module and modules that import it used -/

section

/-!
# `vg_ffdh_check_public` on AArch64: the contract the proofs use

`cpContract` states `Spec.Ffdh.checkPublicContract` on the registers:
`vg_ffdh_check_public(domain = x0, domain_len = x1, p_len = x2, y = x3,
y_len = x4, scratch = x5, scratch_len = x6)`; the shared contract implies it
(`cp_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPublic

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)

def cpPre (s : State) : Prop :=
  let dom : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let y : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let scr : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat * 8⟩
  s.rd = [dom, y] ∧ s.wr = [scr] ∧ dom.Disjoint scr ∧ y.Disjoint scr ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat * 8 ≤ 2 ^ 64 ∧ pLenValid (s.gpr .x2).toNat ∧
    domainLenValid (s.gpr .x2).toNat (s.gpr .x1).toNat ∧ (s.gpr .x4).toNat = (s.gpr .x2).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .x2).toNat ≤ (s.gpr .x6).toNat

/-- The domain on entry. -/
abbrev cpDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat

def cpPost (s s' : State) : Prop :=
  domainValid (s.gpr .x2).toNat (cpDom s) →
    ((s'.gpr .x0).setWidth 32).toNat =
      if publicValid ⟨domainOf (s.gpr .x2).toNat (cpDom s), os2ip (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)⟩
      then 1 else 0

/-- What timing may depend on, beyond the arguments: the domain and y. -/
def cpLeak (s : State) : List Nat :=
  (cpDom s).map (·.toNat) ++ (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat).map (·.toNat)

def cpPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ cpLeak s₁ = cpLeak s₂ ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6

def cpContract : Contract isa where
  pre := cpPre
  post := cpPost
  pub := cpPub

/-- A state meeting the precondition: a 64-byte p, no q. -/
def cpSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 128 | .x2 => 64 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x4000 | .x6 => 1056 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩]
  wr := [⟨0x4000, 8448⟩]

theorem cp_implies : cpContract.Implies (checkPublicContract abi) := by
  sig_implies [checkPublicContract, checkPublicSig, abi, argRegs, cpContract, cpPre, cpPost, cpPub, cpLeak,
    pLenValid, domainLenValid] [cpSat] using cpSat

end VG.Proof.Ffdh.AArch64.CheckPublic

end

end

/-!
# `vg_ffdh_check_public` on AArch64: correctness

From `cpContract`'s precondition, `CheckPublic.code` returns whether y is a
valid public value, for a valid domain (`cp_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPublic

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Spec.Ffdh

/-- What the code uses of the precondition. -/
structure CpCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .x2).toNat
  k2 : (s.gpr .x2).toNat ≤ 1024
  dl : (s.gpr .x1).toNat = 2 * (s.gpr .x2).toNat ∨ (s.gpr .x1).toNat = 3 * (s.gpr .x2).toNat
  yl : (s.gpr .x4).toNat = (s.gpr .x2).toNat
  hZ : 128 * (s.gpr .x2).toNat + 256 ≤ (s.gpr .x6).toNat * 8
  hs : Scr s (s.gpr .x5) ((s.gpr .x6).toNat * 8)
  dom : Src s (s.gpr .x5) ((s.gpr .x6).toNat * 8) (s.gpr .x0) (cpDom s)
  y : Src s (s.gpr .x5) ((s.gpr .x6).toNat * 8) (s.gpr .x3)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)

theorem cpCtx_of {s : State} (h : cpPre s) : CpCtx s := by
  obtain ⟨hrd, hwr, dds, dys, wD, wY, wS, ⟨hk1, hk2⟩, hdl, hyl, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  exact ⟨hk1, hk2, hdl, hyl, by omega_arith, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dds, src_of_region (by rw [hrd]; simp) (by omega_arith) dys⟩

/-- The entry: the arguments into the header at `scratch`. -/
theorem cpEntry_ok {s : State} {B : Addr} (hB : s.gpr .x5 = B) (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8) :
    WP isa (.block CheckPublic.entry) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * sDom) = s.gpr .x0 ∧ word t.mem B (8 * sDomLen) = s.gpr .x1 ∧
      word t.mem B (8 * sK) = s.gpr .x2 ∧ word t.mem B (8 * sY) = s.gpr .x3 ∧
      Outside B (8 * 16) (8 * 4) s.mem t.mem ∧ Keep [.x0] s t := by
  have eD : sDom = 16 := rfl
  have eL : sDomLen = 17 := rfl
  have eK : sK = 18 := rfl
  have eY : sY = 19 := rfl
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = (((s.mem.writeW (off B (8 * sDom)) (s.gpr .x0)).writeW (off B (8 * sDomLen)) (s.gpr .x1)).writeW
        (off B (8 * sK)) (s.gpr .x2)).writeW (off B (8 * sY)) (s.gpr .x3)) (by
    unfold CheckPublic.entry
    brun [Crt.stw, hB, hdr_enc (show sDom < 32 by decide), hdr_enc (show sDomLen < 32 by decide),
      hdr_enc (show sK < 32 by decide), hdr_enc (show sY < 32 by decide), hw sDom (by decide), hw sDomLen (by decide),
      hw sK (by decide), hw sY (by decide)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, k⟩ <;> rw [hm]
  · rw [(writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      (writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      (writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self]
  · rw [(writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      (writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self]
  · rw [(writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self]
  · rw [word_writeW_self]
  · intro x hx
    rw [writeW_outside _ B _ (by omega_arith) x (by omega_arith), writeW_outside _ B _ (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (by omega_arith) x (by omega_arith), writeW_outside _ B _ (by omega_arith) x (by omega_arith)]

/-- With q: its first nonzero octet, `R² mod p`, `y^q mod p` and whether it is 1. -/
theorem cpQ_ok (W : Window) (M : Mont) (S : Selector) {u : State} {B : Addr} {Z k : Nat} {mi : BitVec 64}
    {m₀ : Mem} {dp yp : Addr}
    (hc : SubMem u B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi)
    (hv : XVals u B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)))
    (hval : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)) k = true) (hk1 : 64 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k + 256 ≤ Z) (h0 : u.gpr .x0 = B)
    (hWs : word u.mem B (8 * sWs) = off B (inner ((k + 7) / 8))) (hK : word u.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hQ : word u.mem B (8 * sQ) = dp + BitVec.ofNat 64 (2 * k)) (hY : word u.mem B (8 * sY) = yp)
    (hdom : Src u B Z dp (Spec.Rsa.bytesAt m₀ dp (3 * k)))
    (hy : Src u B Z yp (Spec.Rsa.bytesAt m₀ yp k)) :
    WP isa (seqs (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.subgroup W.code S.code M.mm)) u fun t =>
      t.gpr .x0 = bit (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ yp k) ^
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k) %
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k) = 1) ∧ Keep (.x0 :: mmRegs) u t := by
  obtain hroom := room_k hk1 hZ
  obtain hO : Outer u B Z ((k + 7) / 8) := Outer.of_mem hc h0 hroom (by omega_arith) (by omega_arith)
  obtain hq := src_slice (off := 2 * k) (len := k) hdom (by omega_arith)
  obtain hql : (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k).length = k := bytesAt_length _ _ _
  obtain hne : Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k ≠ [] := by
    intro h; rw [h] at hql; simp at hql; omega_arith
  unfold VG.Impl.Ffdh.AArch64.Domain.CheckPublic.subgroup
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The first nonzero octet of q.
  refine wp_seqs_append (by simp [scan]) (by simp) (WP.mono (scan_ok hO (show sQ < 32 by decide) hQ
    (by rw [hql]; exact hK) hne (by omega_arith) hq) fun u₁ ⟨hEp, hEl, _, f₁, k₁⟩ => ?_)
  have hr₁ := scanR_le
  obtain hc₁ := hc.of_parent f₁ hr₁ k₁.wr
  obtain hv₁ := hv.of_parent hc f₁ (fun r hr => (hr₁ r hr).2)
  obtain hO₁ : Outer u₁ B Z ((k + 7) / 8) := Outer.of_mem hc₁ ((k₁.gpr .x0 (by decide)).trans h0) hroom (by omega_arith)
    (by omega_arith)
  obtain hs₁ : ∀ i < 32, i ≠ sEp → i ≠ sEl → word u₁.mem B (8 * i) = word u.mem B (8 * i) := fun i hi h1 h2 =>
    f₁.word_eq (scanR_word h1 h2) (by omega_using [hi])
  obtain i₁ : InScr B Z u.mem u₁.mem := InScr.of_frm f₁ fun r hr => by
    obtain h1 := (hr₁ r hr).2; omega_using [h1, hZ]
  -- Into the inner workspace, and `R² mod p`.
  obtain hWs₁ : word u₁.mem B (8 * sWs) = off B (inner ((k + 7) / 8)) := by
    rw [hs₁ _ (by decide) (by decide) (by decide)]; exact hWs
  refine wp_seqs_cons (by simp [r2Steps]) (WP.mono (enter_ok hO₁ hWs₁) fun u₂ ⟨⟨h0₂, hm₂⟩, k₂⟩ => ?_)
  obtain hc₂ : SubCtx u₂ B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi :=
    ⟨hc₁.scr.congr k₂.wr, h0₂, by rw [hm₂]; exact hc₁.hdr, by rw [hm₂]; exact hc₁.link, by rw [hm₂]; exact hc₁.nw,
      by rw [hm₂]; exact hc₁.narr, hc₁.lo, hc₁.hi⟩
  obtain hv₂ : XVals u₂ B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)) :=
    ⟨by rw [hm₂]; exact hv₁.n, by rw [hm₂]; exact hv₁.inv, by rw [hm₂]; exact hv₁.one⟩
  refine wp_seqs_append (by simp [r2Steps]) (by simp [pow, Crt.loadArr]) (WP.mono (r2_ctx M hc₂ hv₂ hval hk1 hk2 hZ)
    fun u₃ ⟨hm₃, f₃, k₃⟩ => ?_)
  -- The power and its comparison with 1.
  obtain hlead := lead_lt hne
  rw [hql] at hlead
  obtain ⟨hb₃, hi₃⟩ := child_frm hc₂ (by have := hroom; unfold inner at this ⊢; omega_arith) f₃ (fun r hr => by
    have := r2Ranges_le ((k + 7) / 8) r hr; unfold CrtWindowFive.tabBytes32; omega_arith)
  obtain hw₃ : ∀ i < 32, i ≠ sEp → i ≠ sEl → word u₃.mem B (8 * i) = word u.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hb₃ i hi, hm₂, hs₁ i hi h1 h2]
  obtain hs₃ : InScr B Z u.mem u₃.mem := (i₁.trans (by rw [hm₂]; exact InScr.refl _ _ _)).trans hi₃
  obtain K₃ : Keep (.x0 :: mmRegs) u u₃ :=
    keep_trans (keep_trans (k₁.mono (by decide)) (k₂.mono (by decide))) (k₃.mono (by decide))
  obtain heS := src_slice (off := lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k))
    (len := k - lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k)) hq (by omega_arith)
  rw [← List.append_assoc]
  refine wp_seqs_append (by simp [pow, Crt.loadArr]) (by simp) (WP.mono (powOne_ok W M S hm₃ (bp := sY) (bl := sK)
    (ep := sEp) (el := sEl) (by decide) (by decide) (by decide) (by decide)
    (by rw [hw₃ _ (by decide) (by decide) (by decide)]; exact hY)
    (by rw [hw₃ _ (by decide) (by decide) (by decide), bytesAt_length]; exact hK)
    (hy.congrK hs₃ K₃) (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length])
    (by rw [hb₃ _ (by decide), hm₂]; exact hEp)
    (by rw [hb₃ _ (by decide), hm₂, bytesAt_length, hEl, hql])
    (heS.congrK hs₃ K₃) (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length]; omega_arith))
    fun u₄ ⟨_, h9₄, _, k₄⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (c := .block [mov .x0 .x9]) (Q := fun t => t.gpr .x0 = u₄.gpr .x9) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h0', k₅⟩ => ⟨?_, ?_⟩
  · rw [h0', h9₄]
    obtain e : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k) +
        BitVec.ofNat 64 (lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k)))
        (k - lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k))) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k) := by
      rw [← VG.Proof.Dsa.bytesAt_slice m₀ _ (show lead _ + (k - lead _) ≤ k by omega_arith)]
      generalize Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k = L at hql ⊢
      rw [List.take_of_length_le (by simp; omega_arith), os2ip_drop_lead]
    rw [e]
  · exact keep_trans (keep_trans K₃ (k₄.mono (by decide))) (k₅.mono (by decide))

/-- `publicValid`, on the integers. -/
theorem publicValid_iff (a : Parameters) (y : Nat) :
    publicValid ⟨a, y⟩ = true ↔ (1 < y ∧ y < a.p - 1) ∧ ∀ q, a.q = some q → y ^ q % a.p = 1 := by
  unfold publicValid
  cases hq : a.q with
  | none => simp
  | some q => simp [powMod_eq]

/-- After `domHead`, for a valid modulus p: `main`. -/
theorem cpMain_ok (W : Window) (M : Mont) (S : Selector) {s t : State} (c : CpCtx s)
    (h0 : t.gpr .x0 = s.gpr .x5) (hs : Scr t (s.gpr .x5) ((s.gpr .x6).toNat * 8))
    (hD : word t.mem (s.gpr .x5) (8 * sDom) = s.gpr .x0)
    (hL : word t.mem (s.gpr .x5) (8 * sDomLen) = s.gpr .x1)
    (hK : word t.mem (s.gpr .x5) (8 * sK) = BitVec.ofNat 64 (s.gpr .x2).toNat)
    (hY : word t.mem (s.gpr .x5) (8 * sY) = s.gpr .x3)
    (hQ : word t.mem (s.gpr .x5) (8 * sQ) = s.gpr .x0 + BitVec.ofNat 64 (2 * (s.gpr .x2).toNat))
    (i₀ : InScr (s.gpr .x5) ((s.gpr .x6).toNat * 8) s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hval : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x2).toNat))
      (s.gpr .x2).toNat = true) :
    WP isa (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.main W.code S.code M.mm) t fun t' =>
      (t'.gpr .x0 = if publicValid ⟨domainOf (s.gpr .x2).toNat (cpDom s),
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)⟩ then 1 else 0) ∧
      Keep (.x0 :: mmRegs) t t' := by
  obtain ⟨hk1, hk2, hdl, hyl, hZ, -, hdom, hy⟩ := c
  have hn := hs.nowrap
  simp only [cpDom] at *
  generalize s.gpr .x5 = B at *
  generalize (s.gpr .x6).toNat * 8 = Z at *
  generalize hkk : (s.gpr .x2).toNat = k at *
  rw [hyl] at hy ⊢
  obtain hroom := room_k hk1 hZ
  obtain ⟨hodd, hp1, hlo⟩ := valid_facts hval hk1
  obtain hsrcD := hdom.congr i₀ hrd hwr
  obtain hpS : Src t B Z (s.gpr .x0) (Spec.Rsa.bytesAt s.mem (s.gpr .x0) k) := by
    have := src_slice (off := 0) (len := k) hsrcD (by rcases hdl with h | h <;> rw [h] <;> omega_arith)
    simpa using this
  obtain hyS : Src t B Z (s.gpr .x3) (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) := hy.congr i₀ hrd hwr
  unfold VG.Impl.Ffdh.AArch64.Domain.CheckPublic.main
  rw [show [.block head] ++ pSetup ++ Crt.loadArr aXm sY sK ++ range aXm ++
      [Code.ite (.zero .x .x9) (VG.Impl.Ffdh.AArch64.Domain.ret 0)
        (.seq (.block (leave :: qTest)) (.ite (.zero .x .x3) (VG.Impl.Ffdh.AArch64.Domain.ret 1)
          (seqs (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.subgroup W.code S.code M.mm))))] =
    ([.block head] ++ pSetup) ++ (Crt.loadArr aXm sY sK ++ (range aXm ++
      [Code.ite (.zero .x .x9) (VG.Impl.Ffdh.AArch64.Domain.ret 0)
        (.seq (.block (leave :: qTest)) (.ite (.zero .x .x3) (VG.Impl.Ffdh.AArch64.Domain.ret 1)
          (seqs (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.subgroup W.code S.code M.mm))))])) by
    simp only [List.append_assoc]]
  -- The workspaces.
  refine wp_seqs_append (by simp) (by simp [Crt.loadArr]) (WP.mono (setup_ok hs h0 hk1 hk2 hZ hD hK hpS
    (bytesAt_length _ _ _) hodd) fun u₁ ⟨mi, hc₁, hv₁, hWs₁, f₁, k₁⟩ => ?_)
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  obtain hi8 : 8 * 32 ≤ inner ((k + 7) / 8) := by simp only [inner, slot, hdrBytes]; omega_arith
  obtain hiZ : inner ((k + 7) / 8) + slot ((k + 7) / 8) 8 ≤ Z := by unfold CrtWindowFive.tabBytes32 at hroom; omega_arith
  obtain hp₁ : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word u₁.mem B (8 * i) = word t.mem B (8 * i) := fun i hi h1 h2 h3 =>
    f₁.word_eq (setupR_word _ hi h1 h2 h3) (by omega_using [hi])
  obtain i₁ : InScr B Z t.mem u₁.mem := InScr.of_frm f₁ (setupR_le _ hiZ)
  obtain hY₁ : word u₁.mem B (8 * sY) = s.gpr .x3 := by
    rw [hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hY
  obtain hK₁ : word u₁.mem B (8 * sK) = BitVec.ofNat 64 k := by
    rw [hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hK
  -- y into `aXm`.
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [range, gt1, ltArr, cmpArr])
    (WP.mono (primeLoad_ok hc₁ (by omega_arith) (Nat.le_refl _) (by omega_arith) (show aXm < 8 by decide) (show sY < 32 by decide)
      (show sK < 32 by decide) hY₁ (by rw [bytesAt_length]; exact hK₁) (hyS.congrK i₁ k₁) (by rw [bytesAt_length]; omega_arith)
      (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length])) fun u₂ ⟨hc₂, hy₂, ho₂, k₂⟩ => ?_)
  obtain f₂ : Frm (off B (inner ((k + 7) / 8))) [(slot ((k + 7) / 8) aXm, 8 * ((k + 7) / 8 + 2))] u₁.mem u₂.mem :=
    Frm.of_outside ho₂ (by simp)
  obtain hv₂ := hv₁.of_frmA hc₁.good.scr.nowrap (by omega_arith) f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off _ (by decide) (by decide))
  -- `1 < y < p − 1`.
  refine wp_seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp) (WP.mono (range_ok hc₂.good (Nat.le_refl _)
    (by omega_arith) (by omega_arith) (show aXm < 8 by decide) (by decide) hv₂.one) fun u₃ ⟨h9₃, _, f₃, k₃⟩ => ?_)
  rw [hy₂, hv₂.n] at h9₃
  obtain hpk : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).p =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) k) := domainOf_p _ _ (by rcases hdl with h | h <;> omega_arith)
  obtain hrange : (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) ∧
      2 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) / 2) + 1 <
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) k)) ↔
      (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) <
        (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).p - 1) := by
    rw [hpk, lt_pm1 hodd]
  obtain K₃ : Keep (.x0 :: mmRegs) t u₃ := keep_trans (keep_trans k₁ (k₂.mono (by decide))) (k₃.mono (by decide))
  simp only [seqs]
  refine wp_ite_bit h9₃ (fun hP => ?_) (fun hP => ?_)
  · refine WP.mono (ret_ok u₃ (by decide)) fun t' ⟨⟨h0', _⟩, k'⟩ => ⟨?_, keep_trans K₃ (k'.mono (by decide))⟩
    rw [h0', ite_eq_right (by rw [publicValid_iff]; exact fun h => hP (hrange.mpr h.1))]; rfl
  obtain hR := hrange.mp hP
  -- Back to the outer workspace, and whether there is q.
  obtain r₃ : ∀ r ∈ [(slot ((k + 7) / 8) aTmp, 8 * ((k + 7) / 8)), (8 * sF, 8)], 8 * 17 ≤ r.1 ∧
      r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := fun r hr => ⟨(range_frame _ r hr).1, (range_frame _ r hr).2.1⟩
  obtain hc₃ := hc₂.of_frm f₃ r₃ k₃.wr (k₃.gpr .x0 (by decide))
  obtain hv₃ := hv₂.of_frmA hc₂.good.scr.nowrap (by omega_arith) f₃ (fun r hr => (range_frame _ r hr).2.2)
  obtain ⟨hb₂, hi₂⟩ := child_frm hc₁ (by unfold inner at hroom ⊢; omega_arith) f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := slot_le (w := (k + 7) / 8) (show aXm < 8 by decide)
    unfold CrtWindowFive.tabBytes32; simp only; omega_arith)
  obtain ⟨hb₃, hi₃⟩ := child_frm hc₂ (by unfold inner at hroom ⊢; omega_arith) f₃ (fun r hr => by
    have := r₃ r hr; unfold CrtWindowFive.tabBytes32; omega_arith)
  obtain hw₃ : ∀ i < 32, word u₃.mem B (8 * i) = word u₁.mem B (8 * i) := fun i hi => by rw [hb₃ i hi, hb₂ i hi]
  obtain i₃ : InScr B Z t.mem u₃.mem := (i₁.trans hi₂).trans hi₃
  refine WP.seq (WP.mono (leaveQ_ok hc₃ (dl := (s.gpr .x1).toNat) (k := k)
    (by rw [hw₃ _ (by decide), hp₁ _ (by decide) (by decide) (by decide) (by decide), hL, ofNat_toNat64])
    (by rw [hw₃ _ (by decide)]; exact hK₁) (by rcases hdl with h | h <;> omega_arith)) fun u₄ ⟨⟨h0₄, h3₄, hm₄⟩, k₄⟩ => ?_)
  obtain K₄ : Keep (.x0 :: mmRegs) t u₄ := keep_trans K₃ (k₄.mono (by decide))
  rcases hdl with hdl | hdl
  · -- No q.
    obtain hq : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).q = none := by
      rw [hdl]; exact domainOf_q2 _ _ (by omega_arith)
    refine WP.ite true (by rw [VG.Proof.MlKem.AArch64.eval_zero, h3₄, hdl]; simp) (fun _ => ?_) (fun h => by simp at h)
    refine WP.mono (ret_ok u₄ (by decide)) fun t' ⟨⟨h0', _⟩, k'⟩ => ⟨?_, keep_trans K₄ (k'.mono (by decide))⟩
    rw [h0', ite_eq_left (by rw [publicValid_iff, hq]; exact ⟨hR, fun _ h => by simp at h⟩)]; rfl
  · -- With q.
    obtain hq : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).q =
        some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0 + BitVec.ofNat 64 (2 * k)) k)) := by
      rw [hdl]; exact domainOf_q3 _ _ _
    refine WP.ite false (by
      rw [VG.Proof.MlKem.AArch64.eval_zero, h3₄, hdl]
      rw [show 3 * k - 2 * k = k by omega_arith]
      refine congrArg some (beq_eq_false_iff_ne.mpr fun h => ?_)
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith)] at this; have h00 : k = 0 := this; omega_arith) (fun h => by simp at h)
      (fun _ => ?_)
    obtain hc₄ := hc₃.toMem.congr hm₄ k₄.wr
    obtain hv₄ : XVals u₄ B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) k)) :=
      ⟨by rw [hm₄]; exact hv₃.n, by rw [hm₄]; exact hv₃.inv, by rw [hm₄]; exact hv₃.one⟩
    obtain hw₄ : ∀ i < 32, word u₄.mem B (8 * i) = word u₁.mem B (8 * i) := fun i hi => by rw [hm₄, hw₃ i hi]
    obtain i₄ : InScr B Z t.mem u₄.mem := i₃.trans (by rw [hm₄]; exact InScr.refl _ _ _)
    rw [hdl] at hsrcD
    refine WP.mono (cpQ_ok W M S hc₄ hv₄ hval hk1 hk2 hZ h0₄ (by rw [hw₄ _ (by decide)]; exact hWs₁)
      (by rw [hw₄ _ (by decide)]; exact hK₁)
      (by rw [hw₄ _ (by decide), hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hQ)
      (by rw [hw₄ _ (by decide)]; exact hY₁) (hsrcD.congrK i₄ K₄) (hyS.congrK i₄ K₄))
      fun t' ⟨h0', k'⟩ => ⟨?_, keep_trans K₄ (k'.mono (by decide))⟩
    obtain e : publicValid ⟨domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat),
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k)⟩ = true ↔
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0 + BitVec.ofNat 64 (2 * k)) k) %
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) k) = 1 := by
      rw [publicValid_iff, hq, hpk]
      simp only [Option.some.injEq, forall_eq']
      exact ⟨fun h => h.2, fun h => ⟨hpk ▸ hR, h⟩⟩
    rw [h0']; unfold bit; exact ite_congr (propext e.symm) (fun _ => rfl) (fun _ => rfl)

/-- `vg_ffdh_check_public`. -/
theorem cp_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : cpContract.pre s) :
    ∃ t s', Exec isa (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.code W.code S.code M.mm) s t s' ∧
      abiPreserved s s' ∧ cpContract.post s s' := by
  obtain c := cpCtx_of h
  have hk1 := c.k1
  have hk2 := c.k2
  have hZ := c.hZ
  have hn := c.hs.nowrap
  suffices hwp : WP isa (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.code W.code S.code M.mm) s
      fun s' => abiPreserved s s' ∧ cpContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold VG.Impl.Ffdh.AArch64.Domain.CheckPublic.code
  obtain hw : ∀ i < 22, InRegions s.wr (off (s.gpr .x5) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cpEntry_ok rfl hw) fun t₁ ⟨h0₁, hD₁, hL₁, hK₁, hY₁, ho₁, k₁⟩ => ?_
  obtain i₁ : InScr (s.gpr .x5) ((s.gpr .x6).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega_arith)
  obtain hdom₁ := c.dom.congrK i₁ k₁
  obtain hpS : Src t₁ (s.gpr .x5) ((s.gpr .x6).toNat * 8) (s.gpr .x0)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x2).toNat) := by
    have := src_slice (off := 0) (len := (s.gpr .x2).toNat) hdom₁ (by rcases c.dl with h | h <;> rw [h] <;> omega_arith)
    simpa using this
  refine WP.mono (domHead_ok (c.hs.congr k₁.wr) h0₁ (by omega_arith) hk1 hk2 hD₁ (by rw [hK₁, ofNat_toNat64]) hpS
    (bytesAt_length _ _ _)) fun t₂ ⟨h9₂, hG₂, hQ₂, f₂, h0₂, k₂⟩ => ?_
  obtain hp₂ : ∀ i < 32, i ≠ sG → i ≠ sQ → word t₂.mem (s.gpr .x5) (8 * i) = word t₁.mem (s.gpr .x5) (8 * i) :=
    fun i hi h1 h2 => f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> unfold sG sQ sFn at * <;> omega_arith) (by omega_arith)
  obtain i₂ : InScr (s.gpr .x5) ((s.gpr .x6).toNat * 8) s.mem t₂.mem := i₁.trans (InScr.of_frm f₂ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sG, sQ, sFn] <;> omega_arith)
  obtain K₂ : Keep (.x0 :: mmRegs) s t₂ := keep_trans (k₁.mono (by decide)) (k₂.mono (by decide))
  obtain hpk : (domainOf (s.gpr .x2).toNat (cpDom s)).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0)
      (s.gpr .x2).toNat) := domainOf_p _ _ (by rcases c.dl with h | h <;> omega_arith)
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x2).toNat))
    (s.gpr .x2).toNat) (by rw [eval_zero, h9₂]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x2).toNat))
        (s.gpr .x2).toNat = false := by simpa using hb
    refine WP.mono (ret_ok t₂ (by decide)) fun t' ⟨_, k'⟩ =>
      ⟨abiPreserved_of_keep (keep_trans K₂ (k'.mono (by decide))), fun hd => ?_⟩
    have := domainValid_mod hd
    rw [hpk, hv] at this
    exact absurd this (by decide)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x2).toNat))
        (s.gpr .x2).toNat = true := by simpa using hb
    refine WP.mono (cpMain_ok W M S c h0₂ (c.hs.congr (k₂.wr.trans k₁.wr))
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hD₁)
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hL₁)
      (by rw [hp₂ _ (by decide) (by decide) (by decide), hK₁, ofNat_toNat64])
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hY₁)
      hQ₂ i₂ (k₂.rd.trans k₁.rd) (k₂.wr.trans k₁.wr) hv)
      fun t' ⟨h0', k'⟩ => ⟨abiPreserved_of_keep (keep_trans K₂ k'), fun _ => ?_⟩
    rw [h0']
    split <;> rfl

end VG.Proof.Ffdh.AArch64.CheckPublic

end

end

/-!
# `vg_ffdh_check_public` on AArch64: the stages of a run

Every input of `vg_ffdh_check_public` is public (`CpP`). Between the pieces
of `CheckPublic.code` whose timing the constant-time proof checks, a run from
a state with the public data `p` (`CR p`) satisfies a stage of `p`
(`E1`, `CE`, `C1` … `C8`), by the pieces' correctness. Each stage fixes what
the next piece's addresses, loop counts and branches depend on.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPublic

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Spec.Ffdh

/-- The public data: the working space, the lengths, the pointers, the
domain, y and the stack pointer. -/
structure CpP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  yp : Addr
  dom : List Byte
  yb : List Byte
  sp : Addr

namespace CpP

abbrev w (p : CpP) : Nat := (p.k + 7) / 8

/-- p. -/
abbrev P (p : CpP) : Nat := Spec.Rsa.os2ip (p.dom.take p.k)

/-- q's octets, for a domain with q. -/
abbrev qb (p : CpP) : List Byte := (p.dom.drop (2 * p.k)).take p.k

/-- y. -/
abbrev Y (p : CpP) : Nat := Spec.Rsa.os2ip p.yb

/-- Whether p is a valid modulus. -/
abbrev mv (p : CpP) : Bool := Spec.Rsa.modulusValid p.P p.k

/-- The front's public data. -/
abbrev d (p : CpP) : DPub := ⟨p.B, p.Z, p.k, p.dp⟩

/-- The inner workspace. -/
abbrev ws (p : CpP) : Ws := ⟨off p.B (inner p.w), slot p.w 8, p.w⟩

/-- The header slots the code reads after the entry. -/
abbrev hd (p : CpP) : List (Nat × BitVec 64) :=
  [(sDom, p.dp), (sDomLen, BitVec.ofNat 64 p.dl), (sK, BitVec.ofNat 64 p.k), (sY, p.yp)]

/-- And after `domHead`. -/
abbrev hdQ (p : CpP) : List (Nat × BitVec 64) := p.hd ++ [(sQ, p.dp + BitVec.ofNat 64 (2 * p.k))]

end CpP

/-- A state the contract allows, with the public data `p`. -/
def CR (p : CpP) (s : State) : Prop :=
  cpPre s ∧ s.sp = p.sp ∧ s.gpr .x5 = p.B ∧ (s.gpr .x6).toNat * 8 = p.Z ∧ (s.gpr .x2).toNat = p.k ∧
    (s.gpr .x1).toNat = p.dl ∧ s.gpr .x0 = p.dp ∧ s.gpr .x3 = p.yp ∧ cpDom s = p.dom ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat = p.yb

/-- What a run keeps of its start: the inputs, outside the working space,
and the permissions. -/
def Fx (p : CpP) (t : State) : Prop :=
  ∃ s, CR p s ∧ InScr p.B p.Z s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem Fx.step {p : CpP} {t u : State} (h : Fx p t) (hi : InScr p.B p.Z t.mem u.mem) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) : Fx p u :=
  let ⟨s, hs, i, r, w⟩ := h
  ⟨s, hs, i.trans hi, hrd.trans r, hwr.trans w⟩

theorem Fx.keep {p : CpP} {t u : State} (h : Fx p t) (hi : InScr p.B p.Z t.mem u.mem) {rs : List Reg}
    (k : Keep rs t u) : Fx p u := h.step hi k.rd k.wr

/-- What `Fx` gives. -/
structure FxCtx (p : CpP) (t : State) : Prop where
  scr : Scr t p.B p.Z
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  dl : p.dl = 2 * p.k ∨ p.dl = 3 * p.k
  hZ : 128 * p.k + 256 ≤ p.Z
  dom : Src t p.B p.Z p.dp p.dom
  doml : p.dom.length = p.dl
  y : Src t p.B p.Z p.yp p.yb
  yl : p.yb.length = p.k

theorem Fx.ctx {p : CpP} {t : State} (h : Fx p t) : FxCtx p t := by
  obtain ⟨B, Z, k, dl, dp, yp, dom, yb, sp⟩ := p
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, hdl, hdp, hyp, hdom, hyb⟩, hi, hrd, hwr⟩ := h
  have c := cpCtx_of hpre
  have hy := c.y
  rw [c.yl] at hy hyb
  subst hB hZ hk hdl hdp hyp hdom hyb
  exact ⟨c.hs.congr hwr, c.k1, c.k2, c.dl, c.hZ, c.dom.congr hi hrd hwr, bytesAt_length _ _ _, hy.congr hi hrd hwr,
    bytesAt_length _ _ _⟩

/-! ## The entry and the check of p -/

/-- After the entry. -/
def E1 (p : CpP) (t : State) : Prop := Fx p t ∧ t.gpr .x0 = p.B ∧ Slots t.mem p.B p.hd

/-- The entry's registers. -/
def entryRegs (p : CpP) (r : Reg) : BitVec 64 :=
  if r = .x0 then p.dp else if r = .x1 then BitVec.ofNat 64 p.dl else if r = .x2 then BitVec.ofNat 64 p.k else
    if r = .x3 then p.yp else p.B

theorem cr_regs (p : CpP) (s : State) (h : CR p s) : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x5], s.gpr r = entryRegs p r := by
  obtain ⟨-, -, hB, -, hk, hdl, hdp, hyp, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [entryRegs, reduceCtorEq, ↓reduceIte]
  · exact hdp
  · rw [← hdl, ofNat_toNat64]
  · rw [← hk, ofNat_toNat64]
  · exact hyp
  · exact hB

theorem cr_e1 (p : CpP) (s : State) (h : CR p s) : WP isa (.block CheckPublic.entry) s (E1 p) := by
  have c := cpCtx_of h.1
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have h' := h
  obtain ⟨-, -, hB, hZ', hk, hdl, hdp, hyp, -⟩ := h'
  have hw : ∀ i < 22, InRegions s.wr (off (s.gpr .x5) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  refine WP.mono (cpEntry_ok rfl hw) fun t ⟨h0, hD, hL, hK, hY, ho, k⟩ => ?_
  rw [hB] at h0 hD hL hK hY ho
  rw [hZ'] at hn hZ
  refine ⟨⟨s, h, InScr.of_outside ho (by rw [← hZ']; omega_arith), k.rd, k.wr⟩, h0, ?_⟩
  intro q hq
  simp only [CpP.hd, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact hD.trans hdp
  · rw [hL, ← hdl, ofNat_toNat64]
  · rw [hK, ← hk, ofNat_toNat64]
  · exact hY.trans hyp

theorem e1_dhp (p : CpP) (t : State) (h : E1 p t) : DHP p.d t := by
  obtain ⟨hx, h0, hs⟩ := h
  have c := hx.ctx
  have := c.hZ
  exact ⟨c.scr, h0, show 256 ≤ p.Z by omega_arith, hs (sDom, p.dp) (by simp), hs (sK, BitVec.ofNat 64 p.k) (by simp)⟩

/-- After `domHead`. -/
def CE (p : CpP) (t : State) : Prop :=
  Fx p t ∧ t.gpr .x0 = p.B ∧ Slots t.mem p.B p.hdQ ∧ t.gpr .x9 = BitVec.ofNat 64 p.mv.toNat

/-- What `domHead` changes, within the header. -/
theorem domHeadR_le : ∀ r ∈ [(8 * sG, 8), (8 * sQ, 8)], r.1 + r.2 ≤ 256 := by decide

/-- The header slots read before `domHead` are outside what it changes. -/
theorem hd_domHead (p : CpP) : ∀ q ∈ p.hd,
    q.1 < 32 ∧ ∀ r ∈ [(8 * sG, 8), (8 * sQ, 8)], 8 * q.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * q.1 := by
  rintro ⟨i, v⟩ hq
  dsimp only
  simp only [CpP.hd, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hq
  rcases hq with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

theorem e1_ce (p : CpP) (t : State) (h : E1 p t) : WP isa (.block domHead) t (CE p) := by
  obtain ⟨hx, h0, hs⟩ := h
  have c := hx.ctx
  have hn := c.scr.nowrap
  have hZ := c.hZ
  have hl : (p.dom.take p.k).length = p.k := by rw [List.length_take, c.doml]; rcases c.dl with h | h <;> omega_arith
  refine WP.mono (domHead_ok c.scr h0 (by omega_arith) c.k1 c.k2 (hs (sDom, p.dp) (by simp)) (hs (sK, BitVec.ofNat 64 p.k) (by simp)) (c.dom.take p.k) hl)
    fun u ⟨h9, _, hQ, f, h0', k⟩ => ⟨hx.keep (InScr.of_frm f fun r hr => by
      have h1 := domHeadR_le r hr; omega_using [h1, hZ]) k, h0', ?_, h9⟩
  have hs' : Slots u.mem p.B p.hd := hs.frm f (fun q hq => (hd_domHead p q hq).2) (fun q hq => (hd_domHead p q hq).1)
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hs' q hq
  · rw [List.mem_singleton.mp hq]; exact hQ

theorem ce_eval {p : CpP} {t : State} (h : CE p t) :
    isa.eval (.zero .x .x9) t = some (BitVec.ofNat 64 p.mv.toNat == 0) := by
  rw [eval_zero, h.2.2.2]

theorem ce_valid {p : CpP} {t : State} (h : CE p t) (he : isa.eval (.zero .x .x9) t = some false) : p.mv = true := by
  rw [ce_eval h] at he
  cases hv : p.mv
  · rw [hv] at he; simp at he
  · rfl

theorem ce_setupP (p : CpP) (t : State) (h : CE p t) (he : isa.eval (.zero .x .x9) t = some false) :
    SetupP p.d t := by
  have hv := ce_valid h he
  obtain ⟨hx, h0, hs, -⟩ := h
  have c := hx.ctx
  have hl : (p.dom.take p.k).length = p.k := by rw [List.length_take, c.doml]; rcases c.dl with h | h <;> omega_arith
  obtain ⟨hodd, -⟩ := valid_facts hv c.k1
  exact ⟨p.dom.take p.k, c.scr, h0, c.k1, c.k2, c.hZ, hs (sDom, p.dp) (by simp), hs (sK, BitVec.ofNat 64 p.k) (by simp), c.dom.take p.k, hl, hodd⟩

/-! ## The workspaces, y and its range -/

/-- In the inner workspace for p. -/
def C1 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ SubCtx t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ ∧ p.mv = true

theorem hdQ_lt (p : CpP) : ∀ q ∈ p.hdQ, q.1 < 32 := by
  intro q hq
  simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [sDom, sDomLen, sK, sY, sQ, sFn]

/-- The header slots read after `domHead` are outside what `head` and `pSetup` change. -/
theorem hdQ_setupR (p : CpP) : ∀ q ∈ p.hdQ, ∀ r ∈ setupR p.w, 8 * q.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * q.1 := by
  rintro ⟨i, v⟩ hq
  dsimp only
  simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hq
  rcases hq with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    exact setupR_word _ (by decide) (by decide) (by decide) (by decide)

theorem ce_c1 (p : CpP) (t : State) (h : CE p t) (he : isa.eval (.zero .x .x9) t = some false) :
    WP isa (seqs (([.block head] : List (Prog isa)) ++ pSetup)) t (C1 p) := by
  have hv := ce_valid h he
  obtain ⟨hx, h0, hs, -⟩ := h
  have c := hx.ctx
  have hn := c.scr.nowrap
  have hZ := c.hZ
  have hroom := room_k c.k1 hZ
  have hl : (p.dom.take p.k).length = p.k := by rw [List.length_take, c.doml]; rcases c.dl with h | h <;> omega_arith
  obtain ⟨hodd, -⟩ := valid_facts hv c.k1
  refine WP.mono (setup_ok c.scr h0 c.k1 c.k2 hZ (hs (sDom, p.dp) (by simp)) (hs (sK, BitVec.ofNat 64 p.k) (by simp)) (c.dom.take p.k) hl hodd)
    fun u ⟨mi, hc, hX, hWs, f, k⟩ => ⟨mi, hx.keep (InScr.of_frm f (setupR_le _ (Nat.le_trans (Nat.le_add_right _ _) hroom))) k,
      hc, hX, hWs, hs.frm f (hdQ_setupR p) (hdQ_lt p), hv⟩

/-- In the inner workspace for p, with what the outer one keeps. -/
def In (p : CpP) (mi : BitVec 64) (t : State) : Prop :=
  Fx p t ∧ SubCtx t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ

theorem In.step {p : CpP} {mi : BitVec 64} {t u : State} (h : In p mi t) {rs : List (Nat × Nat)}
    (hf : Frm (off p.B (inner p.w)) rs t.mem u.mem) (hr : ∀ r ∈ rs, StepR p.w r) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) (h0 : u.gpr .x0 = t.gpr .x0) : In p mi u := by
  obtain ⟨hx, hc, hv, hWs, hs⟩ := h
  have c := hx.ctx
  have hroom := room_k c.k1 c.hZ
  rw [show (p.k + 7) / 8 = p.w from rfl] at hroom
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have hGn := hc.good.scr.nowrap
  have hc' := hc.of_frm hf (fun r hr' => ⟨(hr r hr').1, (hr r hr').2.1⟩) hwr h0
  obtain ⟨hb, hi⟩ := child_frm hc (by unfold inner at hroom ⊢; omega_arith) hf (fun r hr' => by
    have := (hr r hr').2.1; omega_arith)
  exact ⟨hx.step hi hrd hwr, hc', hv.of_frmA hGn (by omega_arith) hf (fun r hr' => (hr r hr').2.2),
    by rw [hb _ (by decide)]; exact hWs, fun q hq => by rw [hb _ (hdQ_lt p q hq)]; exact hs q hq⟩

theorem c1_in {p : CpP} {t : State} (h : C1 p t) : ∃ mi, In p mi t ∧ p.mv = true :=
  let ⟨mi, hx, hc, hv, hWs, hs, hm⟩ := h
  ⟨mi, ⟨hx, hc, hv, hWs, hs⟩, hm⟩

/-- y's load. -/
abbrev CpP.yl (p : CpP) : BPub := ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, p.yp, p.k⟩

theorem c1_lpre (p : CpP) (t : State) (h : C1 p t) : LPre aXm sY sK p.yl t := by
  obtain ⟨mi, ⟨hx, hc, -, -, hs⟩, -⟩ := c1_in h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have := c.yl
  exact ⟨mi, p.yb, hc, show 2 ≤ p.w by omega_arith, Nat.le_refl _, show p.w < 2 ^ 30 by omega_arith, by decide, by decide,
    by decide, hs (sY, p.yp) (by simp), by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp), c.yl, c.y,
    by omega_arith, by omega_arith, show (p.yb.length + 7) / 8 ≤ p.w by rw [c.yl]⟩

/-- With y in `aXm`. -/
def C2 (p : CpP) (t : State) : Prop :=
  ∃ mi, In p mi t ∧ p.mv = true ∧ wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = p.Y

theorem c1_c2 (p : CpP) (t : State) (h : C1 p t) : WP isa (seqs (Crt.loadArr aXm sY sK)) t (C2 p) := by
  obtain ⟨mi, hI, hm⟩ := c1_in h
  have hI' := hI
  obtain ⟨hx, hc, -, -, hs⟩ := hI'
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have := c.yl
  refine WP.mono (primeLoad_ok hc (show 2 ≤ p.w by omega_arith) (Nat.le_refl _) (show p.w < 2 ^ 30 by omega_arith)
    (show aXm < 8 by decide) (show sY < 32 by decide) (show sK < 32 by decide) (hs (sY, p.yp) (by simp))
    (by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp)) c.y (by omega_arith) (by omega_arith)
    (show (p.yb.length + 7) / 8 ≤ p.w by rw [c.yl])) fun u ⟨_, hy, ho, k⟩ =>
    ⟨mi, hI.step (rs := [(slot p.w aXm, 8 * (p.w + 2))]) (Frm.of_outside ho (by simp)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact stepR_arr _ (by decide) (by decide) (by decide)) k.rd k.wr
      (k.gpr .x0 (by decide)), hm, hy⟩

theorem c2_goodW1 (p : CpP) (t : State) (h : C2 p t) : GoodW1 p.ws t := by
  obtain ⟨mi, ⟨hx, hc, -⟩, -⟩ := h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  exact ⟨⟨mi, hc.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega_arith, show p.w < 2 ^ 31 by omega_arith⟩

/-- Whether `1 < y < p − 1`, as the code compares. -/
abbrev CpP.rg (p : CpP) : Prop := 1 < p.Y ∧ 2 * (p.Y / 2) + 1 < p.P

/-- After the range check. -/
def C3 (p : CpP) (t : State) : Prop := ∃ mi, In p mi t ∧ p.mv = true ∧ t.gpr .x9 = bit p.rg

theorem c2_c3 (p : CpP) (t : State) (h : C2 p t) : WP isa (seqs (range aXm)) t (C3 p) := by
  obtain ⟨mi, hI, hm, hy⟩ := h
  have hI' := hI
  obtain ⟨hx, hc, hv, -⟩ := hI'
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  refine WP.mono (range_ok hc.good (Nat.le_refl _) (show 1 ≤ p.w by omega_arith) (show p.w < 2 ^ 31 by omega_arith)
    (show aXm < 8 by decide) (by decide) hv.one) fun u ⟨h9, _, f, k⟩ => ⟨mi, hI.step f (fun r hr => ?_) k.rd k.wr
      (k.gpr .x0 (by decide)), hm, by rw [h9, hy, hv.n]⟩
  exact range_frame _ r hr

theorem c3_eval {p : CpP} {t : State} (h : C3 p t) : isa.eval (.zero .x .x9) t = some (bit p.rg == 0) := by
  obtain ⟨_, _, _, h9⟩ := h
  rw [eval_zero, h9]

/-! ## Back to the outer workspace -/

/-- After `leave` and the test of the domain's length. -/
def C4 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ SubMem t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ ∧ p.mv = true ∧ t.gpr .x0 = p.B ∧
    t.gpr .x3 = BitVec.ofNat 64 (p.dl - 2 * p.k)

theorem c3_leave (p : CpP) (t : State) (h : C3 p t) : WP isa (.block [leave]) t fun u => u.gpr .x0 = p.B := by
  obtain ⟨mi, ⟨-, hc, -⟩, -⟩ := h
  exact WP.mono (leave_ok hc) fun u ⟨⟨h0, _⟩, _⟩ => h0

theorem c3_c4 (p : CpP) (t : State) (h : C3 p t) : WP isa (.block (leave :: qTest)) t (C4 p) := by
  obtain ⟨mi, ⟨hx, hc, hv, hWs, hs⟩, hm, -⟩ := h
  have c := hx.ctx
  refine WP.mono (leaveQ_ok hc (hs (sDomLen, BitVec.ofNat 64 p.dl) (by simp)) (hs (sK, BitVec.ofNat 64 p.k) (by simp))
    (by rw [← c.doml]; rcases c.dl with h | h <;> rw [c.doml] <;> omega_arith)) fun u ⟨⟨h0, h3, hmu⟩, k⟩ =>
    ⟨mi, hx.keep (by rw [hmu]; exact InScr.refl _ _ _) k, hc.toMem.congr hmu k.wr,
      ⟨by rw [hmu]; exact hv.n, by rw [hmu]; exact hv.inv, by rw [hmu]; exact hv.one⟩, by rw [hmu]; exact hWs,
      by rw [hmu]; exact hs, hm, h0, h3⟩

theorem c4_eval {p : CpP} {t : State} (h : C4 p t) :
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (p.dl - 2 * p.k) == 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, h3⟩ := h
  rw [eval_zero, h3]

theorem c4_q {p : CpP} {t : State} (h : C4 p t) (he : isa.eval (.zero .x .x3) t = some false) : p.dl = 3 * p.k := by
  have c := h.choose_spec.1.ctx
  rw [c4_eval h] at he
  have := c.k2
  rcases c.dl with hd | hd
  · rw [hd, show 2 * p.k - 2 * p.k = 0 by omega_arith] at he; simp at he
  · exact hd

/-! ## q's first nonzero octet -/

/-- q's octets and their pointer. -/
abbrev CpP.qs (p : CpP) : ScanPub := ⟨p.B, p.Z, p.w, p.dp + BitVec.ofNat 64 (2 * p.k), p.qb⟩

theorem qb_length {p : CpP} {t : State} (c : FxCtx p t) (hq : p.dl = 3 * p.k) : p.qb.length = p.k := by
  simp only [CpP.qb, List.length_take, List.length_drop, c.doml, hq]; omega_arith

theorem c4_scan (p : CpP) (t : State) (h : C4 p t) (he : isa.eval (.zero .x .x3) t = some false) :
    ScanPre sQ p.qs t := by
  have hq := c4_q h he
  obtain ⟨mi, hx, hc, -, -, hs, -, h0, -⟩ := h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have hroom := room_k c.k1 c.hZ
  rw [show (p.k + 7) / 8 = p.w from rfl] at hroom
  have hl := qb_length c hq
  show Outer t p.B p.Z p.w ∧ word t.mem p.B (8 * sQ) = p.dp + BitVec.ofNat 64 (2 * p.k) ∧
    word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.qb.length ∧ p.qb ≠ [] ∧ p.qb.length < 2 ^ 32 ∧
    Src t p.B p.Z (p.dp + BitVec.ofNat 64 (2 * p.k)) p.qb ∧ sQ < 32
  refine ⟨Outer.of_mem hc h0 hroom (by omega_arith) (by omega_arith), hs (sQ, p.dp + BitVec.ofNat 64 (2 * p.k)) (by simp),
    by rw [hl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp), fun he' => by rw [he'] at hl; simp at hl; omega_arith,
    by omega_arith, (c.dom.drop (2 * p.k)).take p.k, by decide⟩

/-- After the scan. -/
def C5 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ SubMem t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ ∧ p.mv = true ∧ t.gpr .x0 = p.B ∧
    p.dl = 3 * p.k ∧ word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead p.qb)

/-- The header slots kept past `scan` are outside what it changes. -/
theorem hdQ_scan (p : CpP) : ∀ q ∈ p.hdQ ++ [(sWs, off p.B (inner p.w))],
    8 * q.1 + 8 ≤ 2 ^ 64 ∧ ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * q.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * q.1 := by
  rintro ⟨i, v⟩ hq
  dsimp only
  simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hq
  rcases hq with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

theorem c4_c5 (p : CpP) (t : State) (h : C4 p t) (he : isa.eval (.zero .x .x3) t = some false) :
    WP isa (seqs (scan sQ)) t (C5 p) := by
  have hq := c4_q h he
  have hS := c4_scan p t h he
  obtain ⟨mi, hx, hc, hv, hWs, hs, hm, h0, -⟩ := h
  have c := hx.ctx
  have hl := qb_length c hq
  have hS' : Outer t p.B p.Z p.w ∧ word t.mem p.B (8 * sQ) = p.dp + BitVec.ofNat 64 (2 * p.k) ∧
      word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.qb.length ∧ p.qb ≠ [] ∧ p.qb.length < 2 ^ 32 ∧
      Src t p.B p.Z (p.dp + BitVec.ofNat 64 (2 * p.k)) p.qb ∧ sQ < 32 := hS
  obtain ⟨hO, hp, hk, hne, hlt, hsrc, -⟩ := hS'
  refine WP.mono (scan_ok hO (show sQ < 32 by decide) hp hk hne hlt hsrc) fun u ⟨hEp, hEl, _, f, k⟩ => ?_
  have hr : ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256 := by decide
  have i : InScr p.B p.Z t.mem u.mem := InScr.of_frm f fun r hr' => by
    have h1 := (hr r hr').2; have h2 := c.hZ; omega_using [h1, h2]
  have hw : ∀ q ∈ p.hdQ ++ [(sWs, off p.B (inner p.w))], word u.mem p.B (8 * q.1) = word t.mem p.B (8 * q.1) :=
    fun q hq => f.word_eq (hdQ_scan p q hq).2 (hdQ_scan p q hq).1
  refine ⟨mi, hx.keep i k, hc.of_parent f hr k.wr, hv.of_parent hc f (fun r hr' => (hr r hr').2),
    by rw [hw (sWs, off p.B (inner p.w)) (by simp)]; exact hWs, fun q hq => by rw [hw q (List.mem_append_left _ hq)]; exact hs q hq,
    hm, (k.gpr .x0 (by decide)).trans h0, hq, hEp, by rw [hEl, hl]⟩

/-! ## `R² mod p`, `y^q mod p` -/

/-- Back in the inner workspace. -/
def C6 (p : CpP) (t : State) : Prop :=
  ∃ mi, In p mi t ∧ p.mv = true ∧ p.dl = 3 * p.k ∧
    word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead p.qb)

theorem c5_x0 {p : CpP} {t : State} (h : C5 p t) : t.gpr .x0 = p.B := h.choose_spec.2.2.2.2.2.2.1

theorem c5_c6 (p : CpP) (t : State) (h : C5 p t) : WP isa (.block [enter]) t (C6 p) := by
  obtain ⟨mi, hx, hc, hv, hWs, hs, hm, h0, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have hroom := room_k c.k1 c.hZ
  rw [show (p.k + 7) / 8 = p.w from rfl] at hroom
  refine WP.mono (enter_ok (Outer.of_mem hc h0 hroom (by omega_arith) (by omega_arith)) hWs) fun u ⟨⟨h0', hmu⟩, k⟩ =>
    ⟨mi, ⟨hx.keep (by rw [hmu]; exact InScr.refl _ _ _) k, (hc.congr hmu k.wr).ctx h0',
      ⟨by rw [hmu]; exact hv.n, by rw [hmu]; exact hv.inv, by rw [hmu]; exact hv.one⟩, by rw [hmu]; exact hWs,
      by rw [hmu]; exact hs⟩, hm, hq, by rw [hmu]; exact hEp, by rw [hmu]; exact hEl⟩

/-- `r2_ok`'s hypotheses, for the run's `-p⁻¹`. -/
theorem c6_r2 {p : CpP} {t : State} {mi : BitVec 64} (hI : In p mi t) (hm : p.mv = true) :
    R2Pre ⟨⟨off p.B (inner p.w), slot p.w 8, p.w, mi⟩, p.P⟩ t := by
  obtain ⟨hx, hc, hv, -⟩ := hI
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  obtain ⟨hodd, -, hlo⟩ := valid_facts hm c.k1
  exact ⟨⟨hc.good, Nat.le_refl _⟩, show 2 ≤ p.w by omega_arith, show p.w < 2 ^ 30 by omega_arith, hv.n, hv.inv, hodd, hlo⟩

/-- After `R² mod p`. -/
def C7 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ ModCtx t p.B p.Z (inner p.w) p.w mi p.P ∧ Slots t.mem p.B p.hdQ ∧ p.dl = 3 * p.k ∧
    word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead p.qb)

theorem c6_c7 (M : Mont) (p : CpP) (t : State) (h : C6 p t) : WP isa (seqs (r2Steps M.mm)) t (C7 p) := by
  obtain ⟨mi, ⟨hx, hc, hv, -, hs⟩, hm, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have hroom := room_k c.k1 c.hZ
  refine WP.mono (r2_ctx M hc hv hm c.k1 c.k2 c.hZ) fun u ⟨hM, f, k⟩ => ?_
  obtain ⟨hb, hi⟩ := child_frm hc (by unfold inner at hroom ⊢; omega_arith) f (fun r hr => by
    have := r2Ranges_le p.w r hr; unfold tabBytes32; omega_arith)
  exact ⟨mi, hx.keep hi k, hM, fun q hq => by rw [hb _ (hdQ_lt p q hq)]; exact hs q hq, hq,
    by rw [hb _ (by decide)]; exact hEp, by rw [hb _ (by decide)]; exact hEl⟩

/-- `pow`'s public data. -/
abbrev CpP.pw (p : CpP) : PowPub :=
  ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, p.yp, p.yb.length, off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb),
    (p.qb.drop (lead p.qb)).length⟩

theorem c7_ps0 (p : CpP) (t : State) (h : C7 p t) : PS0 sY sK sEp sEl p.pw t := by
  obtain ⟨mi, hx, hM, hs, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have hl := qb_length c hq
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have hne : p.qb ≠ [] := fun he => by rw [he] at hl; simp at hl; omega_arith
  have hlead := lead_lt hne
  have := c.yl
  have hsq : Src t p.B p.Z (off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb)) (p.qb.drop (lead p.qb)) :=
    ((c.dom.drop (2 * p.k)).take p.k).drop (lead p.qb)
  exact ps0_of hM (by decide) (by decide) (by decide) (by decide) (hs (sY, p.yp) (by simp))
    (by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp)) c.y (by omega_arith) (by rw [c.yl]) hEp
    (by rw [hEl, List.length_drop, hl]) hsq (by rw [List.length_drop]; omega_arith) (by rw [List.length_drop]; omega_arith)

/-- After `pow`: the inner workspace. -/
def C8 (p : CpP) (t : State) : Prop := GoodW1 p.ws t

theorem c7_c8 (W : Window) (M : Mont) (S : Selector) (p : CpP) (t : State) (h : C7 p t) :
    WP isa (seqs (pow W.code S.code M.mm sY sK sEp sEl)) t (C8 p) := by
  have h0 := c7_ps0 p t h
  obtain ⟨mi, hx, hM, hs, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have hl := qb_length c hq
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have hne : p.qb ≠ [] := fun he => by rw [he] at hl; simp at hl; omega_arith
  have hlead := lead_lt hne
  have := c.yl
  have hsq : Src t p.B p.Z (off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb)) (p.qb.drop (lead p.qb)) :=
    ((c.dom.drop (2 * p.k)).take p.k).drop (lead p.qb)
  exact WP.mono (pow_ok W M S hM (by decide) (by decide) (by decide) (by decide) (hs (sY, p.yp) (by simp))
    (by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp)) c.y (by omega_arith) (by rw [c.yl]) hEp
    (by rw [hEl, List.length_drop, hl]) hsq (by rw [List.length_drop]; omega_arith) (by rw [List.length_drop]; omega_arith))
    fun u ⟨hM', _⟩ => ⟨⟨mi, hM'.sub.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega_arith, show p.w < 2 ^ 31 by omega_arith⟩

end VG.Proof.Ffdh.AArch64.CheckPublic
