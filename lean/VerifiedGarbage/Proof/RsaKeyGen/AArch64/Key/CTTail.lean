module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTLcm
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTLcm
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
meta import VerifiedGarbage.Proof.Rsa.AArch64.Inv
meta import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTCode
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Key
public import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
import VerifiedGarbage.Spec.RsaKeyGen
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Basic.IsEmpty.Defs
meta import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Key
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
meta import VerifiedGarbage.Spec.RsaKeyGen
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Basic.IsEmpty.Defs

/-! ### `RsaKeyGen.AArch64.Key.CTOut`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.AArch64.Key.Out`, which this module and modules that import it used -/

section

/-!
# An RSA key from its primes on AArch64: the outputs

The arrays, masked by `kOk`, to their outputs (`stores_ok`, for any list of
stores to outputs apart from each other), `kOk`'s low bit returned
(`keyExit_ok`), and zeros to the outputs (`zeros_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- The registers the stores change. -/
abbrev stRegs : List Reg := [.x11, .x12, .x8, .x1, .x9, .x15, .x2, .x3, .x5, .x6]

/-- `storeA` under `kOk`, which keeps the working space and the header. -/
theorem storeK_ws {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {out : Addr}
    {c : Bool} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem B (8 * sPtr) = out) (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hm : word s.mem B (8 * kOk) = mask c) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w)
    (hout : ∀ i < len, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < len, Z ≤ ofs B (out + BitVec.ofNat 64 i)) :
    WP isa (seqs (storeA j sPtr sLen kOk)) s fun t =>
      (List.range len).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w j) ((len + 7) / 8) else 0) len ∧
      (∀ x, (∀ i < len, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Ws t B Z w ∧
      Frm B [(Z, 2 ^ 64)] s.mem t.mem ∧ Keep stRegs s t :=
  WP.mono (storeA_ok h hj hP hL (by decide) hp hl hm hl1 hlw hout hsep) fun t ⟨hb, hx, _, _, k⟩ =>
    have hf := frm_scr hsep hx
    ⟨hb, hx, h.congr hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by have := h.h256; omega)) k (by decide), hf, k⟩

/-- A store: the array, the header slots of its output's pointer and length,
the output and its length. -/
structure St where
  j : Nat
  p : Nat
  l : Nat
  out : Addr
  len : Nat

/-- The stores of `L`, in order. -/
def storesK : List St → List (Prog isa)
  | [] => []
  | e :: L => storeA e.j e.p e.l kOk ++ storesK L

/-- A store's hypotheses. -/
structure St.Ok (e : St) (s : State) (B : Addr) (Z w : Nat) : Prop where
  j : e.j < 16
  p : e.p < 32
  l : e.l < 32
  hp : word s.mem B (8 * e.p) = e.out
  hl : word s.mem B (8 * e.l) = BitVec.ofNat 64 e.len
  l1 : 1 ≤ e.len
  lw : e.len ≤ 8 * w
  wr : ∀ i < e.len, InRegions s.wr (e.out + BitVec.ofNat 64 i) 1
  sep : ∀ i < e.len, Z ≤ ofs B (e.out + BitVec.ofNat 64 i)

theorem frm_word {m m' : Mem} {B : Addr} {Z : Nat} (hf : Frm B [(Z, 2 ^ 64)] m m') (hZ : 8 * 32 ≤ Z) {i : Nat}
    (hi : i < 32) : word m' B (8 * i) = word m B (8 * i) :=
  hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega_using [hi])

/-- `St.Ok` after a change below `Z` that keeps the writable regions. -/
theorem St.Ok.congr {e : St} {s t : State} {B : Addr} {Z w : Nat} (ho : e.Ok s B Z w)
    (hf : Frm B [(Z, 2 ^ 64)] s.mem t.mem) (hZ : 8 * 32 ≤ Z) (hwr : t.wr = s.wr) : e.Ok t B Z w :=
  ⟨ho.j, ho.p, ho.l, by rw [frm_word hf hZ ho.p]; exact ho.hp, by rw [frm_word hf hZ ho.l]; exact ho.hl, ho.l1, ho.lw,
    fun i hi => by rw [hwr]; exact ho.wr i hi, ho.sep⟩

/-- The stores of `L`, each output apart from the others. -/
theorem stores_ok {B : Addr} {Z w : Nat} {c : Bool} {Q : State → Prop} :
    ∀ (L : List St) (rest : List (Prog isa)) (s : State), rest ≠ [] → Ws s B Z w →
    word s.mem B (8 * kOk) = mask c → (∀ e ∈ L, e.Ok s B Z w) →
    L.Pairwise (fun a b => Apart a.out a.len b.out b.len) →
    (∀ t, Ws t B Z w → Frm B [(Z, 2 ^ 64)] s.mem t.mem →
      (∀ e ∈ L, (List.range e.len).map (fun i => t.mem (e.out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w e.j) ((e.len + 7) / 8) else 0) e.len) →
      (∀ x, (∀ e ∈ L, ∀ i < e.len, x ≠ e.out + BitVec.ofNat 64 i) → t.mem x = s.mem x) →
      Keep stRegs s t → WP isa (seqs rest) t Q) →
    WP isa (seqs (storesK L ++ rest)) s Q
  | [], rest, s, _, h, _, _, _, k => k s h (Frm.refl _ _ _) (by simp) (fun _ _ => rfl) (Keep.refl _ _)
  | e :: L, rest, s, hr, h, hm, ho, hpw, k => by
    have h256 := h.h256
    obtain ⟨hj, hp, hl, hpv, hlv, hl1, hlw, hwr, hsep⟩ := ho e List.mem_cons_self
    rw [storesK, List.append_assoc]
    refine wp_seqs_append (by simp [storeA]) (by cases L <;> simp [storesK, storeA, hr])
      (WP.mono (storeK_ws h hj hp hl hpv hlv hm hl1 hlw hwr hsep) fun s₁ ⟨b₁, x₁, h₁, f₁, k₁⟩ => ?_)
    have hpw' := List.pairwise_cons.mp hpw
    refine stores_ok L rest s₁ hr h₁ (by rw [frm_word f₁ h256 (by decide)]; exact hm)
      (fun e' he' => (ho e' (List.mem_cons_of_mem _ he')).congr f₁ h256 k₁.wr) hpw'.2
      (fun t ht ft bt xt kt => k t ht (Frm.trans f₁ ft) ?_ ?_ ((k₁.trans kt).mono (by decide)))
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he''
      · rw [← b₁]
        exact List.map_congr_left fun i hi => xt _ fun e'' he''' i' hi' heq =>
          hpw'.1 e'' he''' i (List.mem_range.mp hi) i' hi' heq
      · rw [bt e' he'']
        have hj' := (ho e' (List.mem_cons_of_mem _ he'')).j
        have := (ho e' (List.mem_cons_of_mem _ he'')).lw
        have := h.sl hj'
        have := h.scr.nowrap
        rw [f₁.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega_arith)) (by omega_arith)]
    · intro x hx
      rw [xt x fun e' he' => hx e' (List.mem_cons_of_mem _ he'), x₁ x (hx e List.mem_cons_self)]
termination_by structural L => L

/-- The block that returns `kOk`'s low bit. -/
abbrev retOk : List Instr := [ldh .x3 kOk, movi .x4 1, .logic .and .x .x0 .x3 .x4]

/-- `kOk`'s low bit returned. -/
theorem keyExit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Bool}
    (hm : word s.mem B (8 * kOk) = mask c) :
    WP isa (.block retOk) s fun t =>
      (t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧ t.mem = s.mem) ∧ Keep [.x0, .x3, .x4] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [h256, hi])
  refine WP.keep [.x0, .x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h.x0, hdr_enc (show kOk < 32 by decide), hl kOk (by decide), hm, mask_and_one]

/-- Zeros to each output of `L`. -/
def zerosK (L : List St) : List (Prog isa) := L.map fun e => zeroOut e.p e.l

/-- Zeros to the outputs of `L`, each apart from the others. -/
theorem zeros_ok {B : Addr} {Z w : Nat} {Q : State → Prop} :
    ∀ (L : List St) (rest : List (Prog isa)) (s : State), rest ≠ [] → Ws s B Z w → (∀ e ∈ L, e.Ok s B Z w) →
    L.Pairwise (fun a b => Apart a.out a.len b.out b.len) →
    (∀ t, Ws t B Z w → Frm B [(Z, 2 ^ 64)] s.mem t.mem →
      (∀ e ∈ L, ∀ i < e.len, t.mem (e.out + BitVec.ofNat 64 i) = 0) →
      (∀ x, (∀ e ∈ L, ∀ i < e.len, x ≠ e.out + BitVec.ofNat 64 i) → t.mem x = s.mem x) →
      Keep [.x1, .x2, .x3] s t → WP isa (seqs rest) t Q) →
    WP isa (seqs (zerosK L ++ rest)) s Q
  | [], rest, s, _, h, _, _, k => k s h (Frm.refl _ _ _) (by simp) (fun _ _ => rfl) (Keep.refl _ _)
  | e :: L, rest, s, hr, h, ho, hpw, k => by
    have h256 := h.h256
    obtain ⟨_, hp, hl, hpv, hlv, hl1, hlw, hwr, hsep⟩ := ho e List.mem_cons_self
    have hpw' := List.pairwise_cons.mp hpw
    have hz := zeroOut_ok h.scr h.x0 h256 hp hl hpv hlv hl1 (by have := h.w2; omega_using [hlw, this]) ⟨hwr, hsep⟩
    have step : ∀ s₁, ((∀ i < e.len, s₁.mem (e.out + BitVec.ofNat 64 i) = 0) ∧
        (∀ x, (∀ j < e.len, x ≠ e.out + BitVec.ofNat 64 j) → s₁.mem x = s.mem x) ∧ Keep [.x1, .x2, .x3] s s₁) →
        WP isa (seqs (zerosK L ++ rest)) s₁ Q := by
      intro s₁ ⟨z₁, x₁, k₁⟩
      have f₁ := frm_scr hsep x₁
      have h₁ : Ws s₁ B Z w := h.congr f₁ (fun r hr' => by
        rw [List.mem_singleton.mp hr']; exact Or.inl (by omega)) k₁ (by decide)
      refine zeros_ok L rest s₁ hr h₁ (fun e' he' => (ho e' (List.mem_cons_of_mem _ he')).congr f₁ h256 k₁.wr)
        hpw'.2 (fun t ht ft zt xt kt => k t ht (Frm.trans f₁ ft) ?_ ?_ ((k₁.trans kt).mono (by decide)))
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he₂
        · intro i hi
          rw [xt _ fun e₃ he₃ i' hi' heq => hpw'.1 e₃ he₃ i hi i' hi' heq]
          exact z₁ i hi
        · exact zt e' he₂
      · intro x hx
        rw [xt x fun e' he' => hx e' (List.mem_cons_of_mem _ he'), x₁ x (hx e List.mem_cons_self)]
    rw [zerosK, List.map_cons, List.cons_append]
    have hne : zerosK L ++ rest ≠ [] := by simp [hr]
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    rw [show List.map (fun e => zeroOut e.p e.l) L ++ rest = zerosK L ++ rest from rfl, hcs]
    exact WP.seq (WP.mono hz fun s₁ h₁ => by rw [← hcs]; exact step s₁ h₁)

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-!
# An RSA key from its primes on AArch64: constant time, the outputs

The zeros and the stores take each output's pointer and length from the
header, which correctness pins to the public data (`zeroOutK_ct`,
`storeAK_ct`), and leave the header and the working space as they were
(`EG`: from the stores on, memory outside the working space changes, so
`KS` no longer holds); the exit reads the header.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- From the outputs on: the header and the working space of some inputs
with the public data `p`, with the facts `M`. -/
def EG (M : KIn → State → Prop) (p : KP) (s : State) : Prop :=
  ∃ I, I.pub = p.q ∧ Ws s I.B I.Z I.W ∧ KArgs s.mem I ∧ s.wr = I.Wr ∧ KLens I ∧ KOuts I ∧ M I s

theorem pins_EG (M : KIn → State → Prop) : Pins (EG M) [.x0] := fun _ _ _ ⟨_, e₁, w₁, _⟩ ⟨_, e₂, w₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [w₁.x0, w₂.x0]
  exact (congrArg KQ.B e₁).trans (congrArg KQ.B e₂).symm

theorem EG.of_kg {M : KIn → State → Prop} {p : KP} {s : State} (h : KG M p s) : EG M p s :=
  let ⟨I, _, he, _, hk, L, O, hM⟩ := h
  ⟨I, he, hk.ws, hk.args, hk.wr, L, O, hM⟩

/-- Where an output is, in the header. -/
abbrev OutHdr (sPtr sLen : Nat) (ptr : KQ → Addr) (len : KQ → Nat) : Prop :=
  ∀ I (m : Mem), KArgs m I → KLens I → word m I.B (8 * sPtr) = ptr I.pub ∧
    word m I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub) ∧ (ptr I.pub, len I.pub) ∈ outsL I ∧ 1 ≤ len I.pub ∧
    len I.pub ≤ 8 * I.W

/-- Facts of the header. -/
abbrev HdrStab (M : KIn → State → Prop) : Prop :=
  ∀ I s t, M I s → (∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i)) → M I t

/-- `EG`'s parts after a change outside the working space. -/
theorem EG.after {M : KIn → State → Prop} (hM : HdrStab M) {I : KIn} {s t : State} (hw : Ws s I.B I.Z I.W)
    (ha : KArgs s.mem I) (hW : s.wr = I.Wr) (hm : M I s) (hf : Frm I.B [(I.Z, 2 ^ 64)] s.mem t.mem)
    {rs : List Reg} (k : Keep rs s t) (hr : .x0 ∉ rs) :
    Ws t I.B I.Z I.W ∧ KArgs t.mem I ∧ t.wr = I.Wr ∧ M I t := by
  have h256 := hw.h256
  have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi => frm_word hf h256 hi
  exact ⟨hw.congr hf (fun r hr' => by rw [List.mem_singleton.mp hr']; exact Or.inl (by omega)) k hr,
    ha.congr fun i hi => fw i (by omega_using [hi]), k.wr.trans hW, hM I s t hm fw⟩

theorem zeroOutK_ct {M : KIn → State → Prop} (hM : HdrStab M) {sPtr sLen : Nat} (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : KQ → Addr) (len : KQ → Nat) (hA : OutHdr sPtr sLen ptr len) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 sPtr, ldh .x2 sLen, movi .x3 0]) hc).isSome = true) :
    RelCT isa (Two (EG M)) (zeroOut sPtr sLen) (Two (EG M)) :=
  pin_ct [.x0] [.x1, .x2] (fun p : KP => zoVal (ptr p.q) (len p.q)) (pins_EG M) ht
    (fun p s h => by
      obtain ⟨I, he, hw, ha, -, L, -⟩ := h
      obtain ⟨hp, hl, -⟩ := hA I s.mem ha L
      rw [he] at hp hl
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hw.scr.ld (by omega_using [h256, hi])
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = ptr p.q ∧
        t.gpr .x2 = BitVec.ofNat 64 (len p.q)) (by
        brun [hw.x0, hdr_enc hP, hdr_enc hL, hl' sPtr hP, hl' sLen hL]
        exact ⟨hp, hl⟩) rfl rfl rfl) fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨I, he, hw, ha, hW, L, O, hm⟩ := h
      obtain ⟨hp, hl, ho, hl1, hlw⟩ := hA I s.mem ha L
      have hw2 := hw.w2
      refine WP.mono (zeroOut_ok hw.scr hw.x0 hw.h256 hP hL hp hl hl1 (by omega_using [hlw, hw2])
        ⟨fun i hi => by rw [hW]; exact O.wr _ ho i hi, O.sep _ ho⟩) fun t ⟨_, hx, k⟩ => ?_
      obtain ⟨a, b, c, d⟩ := EG.after hM hw ha hW hm (frm_scr (O.sep _ ho) hx) k (by decide)
      exact ⟨I, he, a, b, c, L, O, d⟩

/-- The block before `storeBE`, with `kOk` the mask (`storeBlk_ok`). -/
theorem storeBlkK_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem B (8 * sPtr) = ptr)
    (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .x8 ++ ([ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 kOk] :
      List Instr))) s fun t => ∀ r ∈ [Reg.x0, .x8, .x1, .x9], t.gpr r = soVal B (off B (slot w j)) ptr len r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok j .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x9, .x15] (Q := fun t => t.gpr .x1 = ptr + BitVec.ofNat 64 len ∧
          t.gpr .x9 = BitVec.ofNat 64 len) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega_using [hi, this])
          brun [h0₃, hdr_enc hP, hdr_enc hL, hdr_enc (show kOk < 32 by decide), m₃, m₂, hl₃ sPtr hP,
            hl₃ sLen hL, hl₃ kOk (by decide), hp, hl])
        rfl rfl rfl)
      fun t ⟨⟨h1, h9⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h9))

theorem storeA_eq (j sPtr sLen : Nat) : seqs (storeA j sPtr sLen kOk) = .seq (.block (ws ++ base j .x8 ++
    ([ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 kOk] : List Instr))) storeBE := rfl

theorem storeAK_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : KQ → Addr)
    (len : KQ → Nat) (hA : OutHdr sPtr sLen ptr len) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++
      ([ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 kOk] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (EG KokM)) (seqs (storeA j sPtr sLen kOk)) (Two (EG KokM)) := by
  rw [storeA_eq]
  refine pin_ct [.x0] [.x0, .x8, .x1, .x9]
    (fun p : KP => soVal p.q.B (off p.q.B (slot p.q.W j)) (ptr p.q) (len p.q)) (pins_EG KokM) ht
    (fun p s h => by
      obtain ⟨I, he, hw, ha, -, L, -⟩ := h
      obtain ⟨hp, hl, -⟩ := hA I s.mem ha L
      rw [← he]
      exact storeBlkK_ok hw hP hL hp hl) (by taint_decide) fun p s h => ?_
  rw [← storeA_eq]
  obtain ⟨I, he, hw, ha, hW, L, O, c, hm⟩ := h
  obtain ⟨hp, hl, ho, hl1, hlw⟩ := hA I s.mem ha L
  refine WP.mono (storeK_ws hw hj hP hL hp hl hm hl1 hlw (fun i hi => by rw [hW]; exact O.wr _ ho i hi)
    (O.sep _ ho)) fun t ⟨_, _, ht, hf, k⟩ => ?_
  have h256 := hw.h256
  have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi => frm_word hf h256 hi
  exact ⟨I, he, ht, ha.congr fun i hi => fw i (by omega_using [hi]), k.wr.trans hW, L, O, c, (fw _ (by decide)).trans hm⟩

/-! ## The outputs' places -/

theorem outN : OutHdr kNo kNl KQ.pN (fun q => 2 * q.pl) := fun I _ ha L =>
  ⟨ha.no, ha.nl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outD : OutHdr kDo kNl KQ.pD (fun q => 2 * q.pl) := fun I _ ha L =>
  ⟨ha.dd, ha.nl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outP : OutHdr kPp kPl KQ.pP KQ.pl := fun I _ ha L =>
  ⟨ha.pp, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outQ : OutHdr kQp kPl KQ.pQ KQ.pl := fun I _ ha L =>
  ⟨ha.qp, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outDp : OutHdr kDp kPl KQ.pDp KQ.pl := fun I _ ha L =>
  ⟨ha.dp, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outDq : OutHdr kDq kPl KQ.pDq KQ.pl := fun I _ ha L =>
  ⟨ha.dq, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outQi : OutHdr kQi kPl KQ.pQi KQ.pl := fun I _ ha L =>
  ⟨ha.qi, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

/-! ## The zeros and the stores -/

theorem zeros2_ct : RelCT isa (Two (EG NF)) (zeros 2) fun _ _ => True := by
  have hM : HdrStab NF := fun _ _ _ _ _ => trivial
  unfold zeros
  simp only [seqs]
  exact RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outN (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outD (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outP (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outQ (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outDp (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outDq (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outQi (by taint_decide))
      (two_taint [.x0] (pins_EG NF) (by taint_decide))))))))

theorem outputs_eq2 : outputs = storeA aQt kNo kNl kOk ++ (storeA aDd kDo kNl kOk ++ (storeA aPa kPp kPl kOk ++
    (storeA aQa kQp kPl kOk ++ (storeA aX₁ kDp kPl kOk ++ (storeA aV kDq kPl kOk ++ (storeA aX₂ kQi kPl kOk ++
    ([.block retOk] : List (Prog isa)))))))) := by
  simp only [outputs, List.append_assoc]

theorem outputs_ct : RelCT isa (Two (EG KokM)) (seqs outputs) fun _ _ => True := by
  rw [outputs_eq2]
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outN
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outD
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outP
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outQ
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outDp
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outDq
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp) (storeAK_ct (by decide) (by decide) (by decide) _ _ outQi
    (by taint_decide)) ?_
  exact two_taint [.x0] (pins_EG KokM) (by taint_decide)

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.Qinv`, which this module and modules that import it used -/

section

/-!
# An RSA key from its primes on AArch64: `qInv`

`qinvPart`: the inverse of `q` modulo `M = p` (3 unless `p` is odd and at
least 3) into `aX₂`, and `kOk &= ` the mask of `gcd(q, M) = 1`
(`qinvPart_k`). The mask `selC` takes is that of the bad case: `p` below 3
or even.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- `qinvPart` before the inverse: `[aU] := q`, `[aM] := ` and `[aV] := ` the
modulus. -/
abbrev qinvPre : List (Prog isa) := [zeroA aU, copyA aU aQa] ++ (constA 3 ++ (ltA aPa aC ++
    (([.block (([mov .x10 .x15] : List Instr) ++ (evenMaskOf aPa ++ ([.logic .orr .x .x15 .x15 .x10] : List Instr))),
      zeroA aM, copyA aM aPa] : List (Prog isa)) ++ (selC aM ++ invFrom aM))))

theorem qinvPart_eq : qinvPart = qinvPre ++
    (([inverseAt halfW aU aV aX₁ aX₂ aM aT] : List (Prog isa)) ++ gcdIsOne) := by
  simp only [qinvPart, qinvPre, List.append_assoc]

/-- The modulus of `qInv`: `p` if it is odd and at least 3, else 3. -/
abbrev qMod (P : Nat) : Nat := if (decide (P % 2 = 1) && !decide (P < 3)) = true then P else 3

/-- The parts `qinvPart` changes. -/
abbrev csQ : List Rc := [.arr aU, .arr aC, .arr aM, .arr aV, .arr aX₁, .arr aX₂, .arr aT, .hdr kOk]

theorem qinv_mask_or (a b : Bool) : mask a ||| mask b = mask (a || b) := by cases a <;> cases b <;> decide

/-- `qMod`, from the mask of the bad case. -/
theorem qMod_bad (P : Nat) : (if (decide (P % 2 = 0) || decide (P < 3)) = true then 3 else P) = qMod P := by
  unfold qMod
  by_cases h1 : P % 2 = 0 <;> by_cases h2 : P < 3 <;>
    simp [h1, h2, show P % 2 = 1 ↔ ¬ P % 2 = 0 by omega_arith]

theorem qMod_odd (P : Nat) : qMod P % 2 = 1 ∧ 1 < qMod P := by
  unfold qMod
  by_cases hc : (decide (P % 2 = 1) && !decide (P < 3)) = true
  · rw [ite_eq_left hc]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hc
    omega_arith
  · rw [ite_eq_right hc]; decide

theorem qMod_lt {P K : Nat} (hP : P < 2 ^ K) (hK : 2 ≤ K) : qMod P < 2 ^ K := by
  unfold qMod
  split
  · exact hP
  · exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hK)

/-- The parts `qinvPre` changes. -/
abbrev csQp : List Rc := [.arr aU, .arr aC, .arr aM, .arr aV, .arr aX₁, .arr aX₂]

/-- `qinvPre`, for `[aPa] = P` and `[aQa] = Q`: `[aU] = Q` and
`[aV] = [aM] = qMod P`. -/
theorem qinvPre_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {P Q : Nat}
    (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) :
    WP isa (seqs qinvPre) s fun t => KS I s₀ t ∧ KF I.B I.W csQp s.mem t.mem ∧
      av I t.mem aU = Q ∧ av I t.mem aV = qMod P ∧ av I t.mem aM = qMod P := by
  have hZ := h.hZ
  simp only [qinvPre]
  -- `[aU] := q`.
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h (o := aU) (a := aQa) (by decide) (by decide)
    (by decide)) fun s₁ ⟨h₁, f₁, v₁, _⟩ => ?_)
  rw [hQ] at v₁
  refine wp_seqs_append (by simp [constA]) (by simp [ltA, cmpA]) (WP.mono (constA_k h₁ (x := 3) (by decide))
    fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  obtain c3 : av I s₂.mem aC = 3 :=
    av_of_full c₂ (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide)
      (show 2 ≤ 64 * I.W by have := h.ws.w1; omega_arith)))
  obtain vP₂ : av I s₂.mem aPa = P := by
    rw [f₂.av (by decide) (by decide) (by decide) hZ, f₁.av (by decide) (by decide) (by decide) hZ, hP]
  refine wp_seqs_append (by simp [ltA, cmpA]) (by simp) (WP.mono (ltA_k h₂ (a := aPa) (b := aC) (by decide)
    (by decide)) fun s₃ ⟨h₃, m₃, h15₃, _, _⟩ => ?_)
  rw [vP₂, c3] at h15₃
  generalize hpv : (decide (P % 2 = 0) || decide (P < 3)) = pv
  -- `x15 := ` the mask of `p` even or below 3; `[aM] := p`.
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.x10]
    (Q := fun t => t.gpr .x10 = mask (decide (P < 3)) ∧ t.mem = s₃.mem) (by brun [h15₃]) (by decide) (by decide)
      (by decide +kernel)) fun s₄ ⟨⟨h10₄, m₄⟩, k₄⟩ => WP.block_append_iff.mpr ?_))
  obtain h₄ := h₃.regs m₄ k₄
  refine WP.mono (evenMaskOf_k h₄ (j := aPa) (by decide)) fun s₅ ⟨h₅, m₅, h15₅, _, _, k₅⟩ => ?_
  rw [m₄, m₃, vP₂] at h15₅
  obtain h10₅ : s₅.gpr .x10 = mask (decide (P < 3)) := by rw [k₅.gpr .x10 (by decide), h10₄]
  refine WP.mono (WP.keep [.x15] (Q := fun t => t.gpr .x15 = mask pv ∧ t.mem = s₅.mem) (by
    brun [h15₅, h10₅, qinv_mask_or]; rw [hpv]) (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨⟨h15₆, m₆⟩, k₆⟩ => ?_
  obtain h₆ := h₅.regs m₆ k₆
  obtain hm₆ : s₆.mem = s₂.mem := by rw [m₆, m₅, m₄, m₃]
  refine WP.seq (WP.mono (zeroA_k h₆ (j := aM) (by decide)) fun s₇ ⟨h₇, f₇, _, _, k₇⟩ =>
    WP.mono (copyA_k h₇ (o := aM) (a := aPa) (by decide) (by decide) (by decide)) fun s₈ ⟨h₈, f₈, v₈, _, k₈⟩ => ?_)
  obtain vP₆ : av I s₆.mem aPa = P := by rw [hm₆, vP₂]
  rw [f₇.av (by decide) (by decide) (by decide) hZ, vP₆] at v₈
  obtain vC₈ : av I s₈.mem aC = 3 := by
    rw [f₈.av (by decide) (by decide) (by decide) hZ, f₇.av (by decide) (by decide) (by decide) hZ, hm₆, c3]
  -- `[aM] := M`.
  refine wp_seqs_append (by simp [selC]) (by simp [invFrom]) (WP.mono (selC_k h₈ (j := aM) (by decide) (by decide)
    (c := pv) (by rw [k₈.gpr .x15 (by decide), k₇.gpr .x15 (by decide), h15₆])) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ => ?_)
  rw [v₈, vC₈] at v₉
  obtain hM : (if pv = true then 3 else P) = qMod P := by rw [← hpv]; exact qMod_bad P
  rw [hM] at v₉
  -- `[aV] := [aM]`.
  refine WP.mono (invFrom_k h₉ (j := aM) (by decide) (by decide)) fun s₁₀ ⟨h₁₀, f₁₀, vV₁₀, _, _⟩ => ?_
  obtain hok10 : [Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂].all Rc.ok = true := by decide
  obtain vM₁₀ : av I s₁₀.mem aM = qMod P := by rw [f₁₀.av hok10 (by decide) (by decide) hZ, v₉]
  obtain vU₁₀ : av I s₁₀.mem aU = Q := by
    rw [f₁₀.av hok10 (by decide) (by decide) hZ, f₉.av (by decide) (by decide) (by decide) hZ,
      f₈.av (by decide) (by decide) (by decide) hZ, f₇.av (by decide) (by decide) (by decide) hZ, hm₆,
      f₂.av (by decide) (by decide) (by decide) hZ, v₁]
  obtain f₂₆ : KF I.B I.W [.arr aC] s₁.mem s₆.mem := by rw [hm₆]; exact f₂
  exact ⟨h₁₀, ((((f₁.trans f₂₆).trans f₇).trans f₈).trans f₉).trans f₁₀ |>.mono (by decide), vU₁₀,
    by rw [vV₁₀, v₉], vM₁₀⟩

/-- `qinvPart`, for `[aPa] = P` and `[aQa] = Q` of the primes' `w` words. -/
theorem qinvPart_k [VG.Proof.Rsa.AArch64.InvLaw] {I : KIn} {s₀ s : State} (h : KS I s₀ s) (L : KLens I) {P Q : Nat}
    {ok : Bool} (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (hPw : P < 2 ^ (64 * (I.pl / 8)))
    (hQw : Q < 2 ^ (64 * (I.pl / 8))) (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs qinvPart) s fun t => KS I s₀ t ∧ KF I.B I.W csQ s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd Q (qMod P) = 1) && ok) ∧
      ((qMod P : Nat) : Int) ∣ (av I t.mem aX₂ : Int) * Q - Nat.gcd Q (qMod P) ∧ av I t.mem aX₂ < qMod P := by
  have hZ := h.hZ
  have hl1 := L.pl1
  rw [qinvPart_eq]
  refine wp_seqs_append (by simp [qinvPre]) (by simp) (WP.mono (qinvPre_k h hP hQ)
    fun s₁₀ ⟨h₁₀, f₁₀, vU₁₀, vV₁₀, vM₁₀⟩ => ?_)
  obtain hMo := qMod_odd P
  -- The inverse, at the primes' width.
  refine wp_seqs_append (by simp) (by simp [gcdIsOne, constA]) ?_
  simp only [seqs]
  refine WP.mono (inverseHalf_k h₁₀ L (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aM) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [vU₁₀]; exact hQw)
    (by rw [vM₁₀]; exact qMod_lt hPw (by omega_arith)) (by rw [vV₁₀, vM₁₀])) fun s₁₁ ⟨h₁₁, f₁₁, _, hinv⟩ => ?_
  rw [vM₁₀, vU₁₀] at hinv
  obtain ⟨hg₁₁, hdv₁₁, hx₁₁⟩ := hinv hMo.1 hMo.2
  obtain hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT].all Rc.ok = true := by decide
  obtain ok₁₁ : word s₁₁.mem I.B (8 * kOk) = mask ok := by
    rw [f₁₁.word hokI (by decide) (by decide), f₁₀.word (by decide) (by decide) (by decide), hok]
  refine WP.mono (gcdIsOne_k h₁₁ ok₁₁) fun t ⟨ht, f₁₂, ok₁₂⟩ => ?_
  rw [hg₁₁] at ok₁₂ hdv₁₁
  obtain vX : av I t.mem aX₂ = av I s₁₁.mem aX₂ := f₁₂.av (by decide) (by decide) (by decide) hZ
  refine ⟨ht, ?_, ok₁₂, by rw [vX]; exact hdv₁₁, by rw [vX]; exact hx₁₁⟩
  exact ((f₁₀.trans f₁₁).trans f₁₂).mono (by decide)

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.Crt`, which this module and modules that import it used -/

section

/-!
# An RSA key from its primes on AArch64: `dP` and `dQ`

`crtPart`: `dP = d mod (p − 1)` into `aX₁` and `dQ = d mod (q − 1)` into
`aV`, each divisor 1 for 0 (`divisorOf_k`; `crtPart_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- The parts `crtPart` changes. -/
abbrev csC : List Rc := [.arr aM, .arr aC, .arr aU, .arr aV, .arr aT, .arr aX₁]

/-- `crtPart`: `[aX₁] := d mod dv(P − 1)`, `[aV] := d mod dv(Q − 1)`, for `[aDd] = d`,
`[aPm] = P − 1` and `[aQm] = Q − 1`. -/
theorem crtPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {d a b : Nat} (hd : av I s.mem aDd = d)
    (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) :
    WP isa (seqs crtPart) s fun t => KS I s₀ t ∧ KF I.B I.W csC s.mem t.mem ∧
      av I t.mem aX₁ = d % dv a ∧ av I t.mem aV = d % dv b := by
  have hZ := h.hZ
  obtain hdv : ∀ x, 0 < dv x := fun x => by unfold dv; split <;> omega_arith
  unfold crtPart
  simp only [List.append_assoc]
  -- `dP`.
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h (j := aPm) (by decide) (by decide)
    (by decide)) fun s₁ ⟨h₁, f₁, v₁⟩ => ?_)
  rw [ha] at v₁
  obtain hok1 : [Rc.arr aM, Rc.arr aC].all Rc.ok = true := by decide
  obtain vD₁ : av I s₁.mem aDd = d := by rw [f₁.av hok1 (by decide) (by decide) hZ, hd]
  refine wp_seqs_append (by simp) (by simp [divisorOf]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aU) (by decide)) fun s₂ ⟨h₂, f₂, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aU) (a := aDd) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₃ (iQ := aU) (iR := aV) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, d₄⟩ =>
        WP.seq (WP.mono (zeroA_k h₄ (j := aX₁) (by decide)) fun s₅ ⟨h₅, f₅, _, _⟩ =>
          WP.mono (copyA_k h₅ (o := aX₁) (a := aV) (by decide) (by decide) (by decide))
            fun s₆ ⟨h₆, f₆, v₆, _, _⟩ => ?_))))
  obtain vM₃ : av I s₃.mem aM = dv a := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, v₁]
  obtain vU₃ : av I s₃.mem aU = d := by rw [v₃, f₂.av (by decide) (by decide) (by decide) hZ, vD₁]
  rw [vM₃, vU₃] at d₄
  obtain hR := (d₄ (hdv a)).1
  obtain hlt : d % dv a < dv a := Nat.mod_lt _ (hdv a)
  obtain vM₁W : dv a < 2 ^ (64 * I.W) := by rw [← v₁]; exact wv_lt _ _ _ _
  obtain vX₆ : av I s₆.mem aX₁ = d % dv a := by
    rw [v₆, f₅.av (by decide) (by decide) (by decide) hZ, ← hR]
    exact wv_low_of_lt (by omega_using []) (by rw [hR]; omega_using [hlt, vM₁W])
  obtain hok4 : [Rc.arr aU, Rc.arr aV, Rc.arr aT].all Rc.ok = true := by decide
  obtain pres6 : ∀ j, j < 16 → j ≠ aU → j ≠ aV → j ≠ aT → j ≠ aX₁ → av I s₆.mem j = av I s₁.mem j :=
    fun j hj h1 h2 h3 h4 => by
      rw [f₆.av (by decide) hj (by simp [h4]) hZ, f₅.av (by decide) hj (by simp [h4]) hZ,
        f₄.av hok4 hj (by simp [h1, h2, h3]) hZ, f₃.av (by decide) hj (by simp [h1]) hZ,
        f₂.av (by decide) hj (by simp [h1]) hZ]
  obtain vQm₆ : av I s₆.mem aQm = b := by
    rw [pres6 aQm (by decide) (by decide) (by decide) (by decide) (by decide), f₁.av hok1 (by decide) (by decide) hZ,
      hb]
  obtain vD₆ : av I s₆.mem aDd = d := by
    rw [pres6 aDd (by decide) (by decide) (by decide) (by decide) (by decide), vD₁]
  -- `dQ`.
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h₆ (j := aQm) (by decide) (by decide)
    (by decide)) fun s₇ ⟨h₇, f₇, v₇⟩ => ?_)
  rw [vQm₆] at v₇
  obtain vD₇ : av I s₇.mem aDd = d := by rw [f₇.av hok1 (by decide) (by decide) hZ, vD₆]
  obtain vX₇ : av I s₇.mem aX₁ = d % dv a := by rw [f₇.av hok1 (by decide) (by decide) hZ, vX₆]
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aU) (by decide)) fun s₈ ⟨h₈, f₈, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₈ (o := aU) (a := aDd) (by decide) (by decide) (by decide)) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ =>
      WP.mono (divmod_k h₉ (iQ := aU) (iR := aV) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        fun t ⟨ht, f₁₀, d₁₀⟩ => ?_))
  obtain vM₉ : av I s₉.mem aM = dv b := by
    rw [f₉.av (by decide) (by decide) (by decide) hZ, f₈.av (by decide) (by decide) (by decide) hZ, v₇]
  obtain vU₉ : av I s₉.mem aU = d := by rw [v₉, f₈.av (by decide) (by decide) (by decide) hZ, vD₇]
  rw [vM₉, vU₉] at d₁₀
  obtain hR' := (d₁₀ (hdv b)).1
  obtain vMb : dv b < 2 ^ (64 * I.W) := by rw [← v₇]; exact wv_lt _ _ _ _
  refine ⟨ht, ?_, ?_, ?_⟩
  · exact (((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇).trans f₈).trans f₉).trans
      f₁₀).mono (by decide)
  · rw [f₁₀.av hok4 (by decide) (by decide) hZ, f₉.av (by decide) (by decide) (by decide) hZ,
      f₈.av (by decide) (by decide) (by decide) hZ, vX₇]
  · rw [← hR']
    exact wv_low_of_lt (by omega_using []) (by rw [hR']; exact Nat.lt_trans (Nat.mod_lt _ (hdv b)) vMb)

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.NFin`, which this module and modules that import it used -/

section

/-!
# An RSA key from its primes on AArch64: `n` and the final mask

`n = p q` (`nPart_k`), and `kOk &= ` the masks of `n`'s top bit, `p` and
`q` odd, and `e` valid, and'ed in `x10` (`finalMask_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- `nPart`: `[aQt] := [aPa] [aQa]`, `w` words each, for `W = 2 w`. -/
theorem nPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPa = a) (hb : av I s.mem aQa = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs nPart) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aQt] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aQt) (I.W + 2) = a * b :=
  mulTo_k h hW (o := aQt) (a := aPa) (b := aQa) (by decide) (by decide) (by decide) (by decide) (by decide)
    ha hb ha' hb'

/-! ## The final mask -/

/-- The top bit of a `W`-word number: of its word `W − 1`. -/
theorem top_bit_k {m : Mem} {B : Addr} {d W : Nat} (hW : 1 ≤ W) :
    (word m B (d + 8 * (W - 1))).toNat / 2 ^ 63 = if 2 ^ (64 * W - 1) ≤ wv m B d W then 1 else 0 := by
  obtain e : wv m B d W = wv m B d (W - 1) + 2 ^ (64 * (W - 1)) * (word m B (d + 8 * (W - 1))).toNat := by
    rw [show W = W - 1 + 1 from by omega_arith, wv]; simp
  obtain ha := wv_lt m B d (W - 1)
  obtain ht := (word m B (d + 8 * (W - 1))).isLt
  generalize wv m B d (W - 1) = a at e ha
  generalize (word m B (d + 8 * (W - 1))).toNat = t at e ht
  obtain hp : 2 ^ (64 * W - 1) = 2 ^ (64 * (W - 1)) * 2 ^ 63 := by rw [← Nat.pow_add]; congr 1; omega_arith
  generalize 2 ^ (64 * (W - 1)) = R at e ha hp
  rw [e, hp]
  by_cases h63 : 2 ^ 63 ≤ t
  · have : R * 2 ^ 63 ≤ R * t := Nat.mul_le_mul_left _ h63
    rw [ite_eq_left (show R * 2 ^ 63 ≤ a + R * t by omega_arith)]; omega_arith
  · have : R * t + R ≤ R * 2 ^ 63 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega_arith)
    rw [ite_eq_right (show ¬ R * 2 ^ 63 ≤ a + R * t by omega_arith)]; omega_arith

/-- The mask of a word's top bit. -/
theorem shr63_mask_k (x : BitVec 64) :
    BitVec.setWidth 64 (0#16) - x >>> 63 = mask (decide (x.toNat / 2 ^ 63 = 1)) := by
  obtain h : x >>> 63 = BitVec.ofNat 64 (x.toNat / 2 ^ 63) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := x.isLt; omega_arith
  rw [h]
  have := x.isLt
  rcases (show x.toNat / 2 ^ 63 = 0 ∨ x.toNat / 2 ^ 63 = 1 by omega_arith) with e | e <;> rw [e] <;> decide

theorem ite_mask_k (c : Bool) : (if c = true then mask true else mask false) = mask c := by cases c <;> rfl

theorem ite_mask_not_k (c : Bool) : (if (!c) = true then mask false else mask true) = mask c := by cases c <;> rfl

/-- The mask `finalMask` leaves in `kOk`. -/
abbrev finalOk (W n P Q e : Nat) (ok : Bool) : Bool :=
  decide (2 ^ (64 * W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) && Spec.Rsa.exponentValid e

/-- `finalMask`'s pieces: the top bit and `ok`, an `and` of `x15`, and the
three tests of `e`. -/
def finTop : List Instr :=
  [.lsl .x .x3 .x12 3, .add .x .x16 .x16 .x3, .subImm .x .x16 .x16 8, ld .x3 .x16, .lsr .x .x3 .x3 63, movi .x7 0,
    .sub .x .x10 .x7 .x3, ldh .x3 kOk, .logic .and .x .x10 .x10 .x3]
def finAnd : List Instr := [.logic .and .x .x10 .x10 .x15]
def finE1 : List Instr := [ldh .x3 kEv] ++ oddMask ++ finAnd
def finE2 : List Instr := [ldh .x3 kEv, movi .x4 3, .subs .x .x3 .x3 .x4]
def finE3 : List Instr := [ldh .x3 kEv, .lsr .x .x3 .x3 33, movi .x4 1, .subs .x .x3 .x3 .x4]
def finSt : List Instr := [.logic .and .x .x10 .x10 .x15, sth .x10 kOk]

theorem finalMask_eq : finalMask = ws ++ (base aQt .x16 ++ (finTop ++ (oddMaskOf aPa ++ (finAnd ++ (oddMaskOf aQa ++
    (finAnd ++ (finE1 ++ (finE2 ++ ((carryMask ++ finAnd) ++ (finE3 ++ (borrowMask ++ finSt))))))))))) := by
  simp only [finalMask, finTop, finAnd, finE1, finE2, finE3, finSt, List.append_assoc, List.cons_append,
    List.nil_append]

/-- `finalMask`, for `[aQt] = n`, `[aPa] = P`, `[aQa] = Q` and `kOk` the
mask of `ok`. -/
theorem finalMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {n P Q e : Nat} {ok : Bool}
    (hn : av I s.mem aQt = n) (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (he64 : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (.block finalMask) s fun t => KS I s₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (finalOk I.W n P Q e ok) := by
  have hnw := h.ws.scr.nowrap
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
  have hw2 := h.ws.w2
  obtain sN := h.ws.sl (j := aQt) (by decide)
  have h256 := h.ws.h256
  rw [finalMask_eq, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h aQt) fun s₁ ⟨⟨h16, h12, _, m₁⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  obtain hs₁ := h.ws.scr.congr k₁.wr
  obtain h0₁ : s₁.gpr .x0 = I.B := (k₁.gpr .x0 (by decide)).trans h.ws.x0
  obtain htop : (word s.mem I.B (slot I.W aQt + 8 * (I.W - 1))).toNat / 2 ^ 63 = 1 ↔ 2 ^ (64 * I.W - 1) ≤ n := by
    rw [top_bit_k hw1, show wv s.mem I.B (slot I.W aQt) I.W = n from hn]; split <;> simp_all
  have hok' : s.mem.readW (off I.B (8 * kOk)) 64 = mask ok := hok
  -- `x10 := ` the masks of the top bit and `ok`.
  refine WP.mono (WP.keep [.x3, .x7, .x10, .x16] (Q := fun t =>
      t.gpr .x10 = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok) ∧ t.mem = s.mem) (by
    brun [finTop, h16, h12, h0₁, m₁, top_addr I.B (d := slot I.W aQt) (w := I.W) hw1 (by omega_arith),
      hs₁.ld (d := slot I.W aQt + 8 * (I.W - 1)) (by omega_arith), hdr_enc (show kOk < 32 by decide),
      hs₁.ld (d := 8 * kOk) (by unfold kOk sFn; omega_arith), shr63_mask_k, hok', mask_and', decide_eq_decide.mpr htop])
    (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h10₂, m₂⟩, k₂⟩ => WP.block_append_iff.mpr ?_
  obtain h₂ := h.regs m₂ (k₁.trans k₂)
  -- `p` odd.
  refine WP.mono (oddMaskOf_k h₂ (j := aPa) (by decide)) fun s₃ ⟨h₃, m₃, h15₃, _, _, _, k₃⟩ =>
    WP.block_append_iff.mpr ?_
  rw [m₂, hP] at h15₃
  obtain h10₃ : s₃.gpr .x10 = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok) := by rw [k₃.gpr .x10 (by decide), h10₂]
  refine WP.mono (WP.keep [.x10] (Q := fun t => t.gpr .x10 = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok &&
    decide (P % 2 = 1)) ∧ t.mem = s₃.mem) (by brun [finAnd, h15₃, h10₃, mask_and']) (by decide) (by decide)
      (by decide +kernel)) fun s₄ ⟨⟨h10₄, m₄⟩, k₄⟩ => WP.block_append_iff.mpr ?_
  obtain h₄ := h₃.regs m₄ k₄
  -- `q` odd.
  refine WP.mono (oddMaskOf_k h₄ (j := aQa) (by decide)) fun s₅ ⟨h₅, m₅, h15₅, h7₅, _, _, k₅⟩ => ?_
  rw [m₄, m₃, m₂, hQ] at h15₅
  obtain h10₅ : s₅.gpr .x10 = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1)) := by
    rw [k₅.gpr .x10 (by decide), h10₄]
  obtain hm₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂]
  have hs₅ := h₅.ws.scr
  have h0₅ : s₅.gpr .x0 = I.B := h₅.x0
  obtain hev₅ : s₅.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [hm₅]; exact hev
  obtain hte : (BitVec.ofNat 64 e).toNat = e := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
  -- `q` odd.
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x10] (Q := fun t => t.gpr .x10 =
      mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1)) ∧ t.mem = s₅.mem) (by
    brun [finAnd, h15₅, h10₅, mask_and']) (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨⟨h10₆, m₆⟩, k₆⟩ => WP.block_append_iff.mpr ?_)
  obtain hev₆ : s₆.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [m₆]; exact hev₅
  obtain h0₆ : s₆.gpr .x0 = I.B := (k₆.gpr .x0 (by decide)).trans h0₅
  obtain h7₆ : s₆.gpr .x7 = 0 := (k₆.gpr .x7 (by decide)).trans h7₅
  obtain hs₆ := hs₅.congr k₆.wr
  -- `e` odd.
  refine WP.mono (WP.keep [.x3, .x4, .x10, .x15] (Q := fun t => t.gpr .x10 =
      mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) &&
        decide (e % 2 = 1)) ∧ t.mem = s₆.mem ∧ t.gpr .x7 = 0) (by
    brun [finE1, oddMask, finAnd, h0₆, h7₆, hdr_enc (show kEv < 32 by decide),
      hs₆.ld (d := 8 * kEv) (by unfold kEv sFn; omega_arith), hev₆, h10₆, mask_low, mask_low', hte, mask_and'])
    (by decide) (by decide) (by decide +kernel)) fun s₇ ⟨⟨h10₇, m₇, h7₇⟩, k₇⟩ => WP.block_append_iff.mpr ?_
  obtain hev₇ : s₇.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [m₇]; exact hev₆
  obtain h0₇ : s₇.gpr .x0 = I.B := (k₇.gpr .x0 (by decide)).trans h0₆
  obtain hs₇ := hs₆.congr k₇.wr
  -- `e ≥ 3`: the carry, its mask, and'ed.
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.c = decide (3 ≤ e) ∧ t.mem = s₇.mem) (by
    brun [finE2, h0₇, hdr_enc (show kEv < 32 by decide), hs₇.ld (d := 8 * kEv) (by unfold kEv sFn; omega_arith), hev₇]
    rw [BitVec.toNat_not, show (BitVec.setWidth 64 3#16 : BitVec 64).toNat = 3 from rfl, Bool.toNat_true, hte]
    exact decide_eq_decide.mpr (by omega_arith))
    (by decide) (by decide) (by decide +kernel)) fun s₈ ⟨⟨c₈, m₈⟩, k₈⟩ => WP.block_append_iff.mpr ?_
  obtain h10₈ := (k₈.gpr .x10 (by decide)).trans h10₇
  obtain h7₈ := (k₈.gpr .x7 (by decide)).trans h7₇
  refine WP.mono (WP.keep [.x4, .x10, .x15] (Q := fun t => t.gpr .x10 =
      mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) &&
        decide (e % 2 = 1) && decide (3 ≤ e)) ∧ t.mem = s₈.mem) (by
    brun [carryMask, finAnd, h7₈, h10₈, c₈]
    rw [show (0 : BitVec 64) - 1#64 = mask true from rfl, show (0 : BitVec 64) = mask false from rfl, ite_mask_k,
      mask_and'])
    (by decide) (by decide) (by decide +kernel)) fun s₉ ⟨⟨h10₉, m₉⟩, k₉⟩ => WP.block_append_iff.mpr ?_
  obtain hev₉ : s₉.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [m₉, m₈]; exact hev₇
  obtain h0₉ : s₉.gpr .x0 = I.B := ((k₈.trans k₉).gpr .x0 (by decide)).trans h0₇
  obtain hs₉ := hs₇.congr (k₈.trans k₉).wr
  -- `e < 2^33`: the borrow of `(e >> 33) − 1`.
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.c = !decide (e < 2 ^ 33) ∧ t.mem = s₉.mem) (by
    brun [finE3, h0₉, hdr_enc (show kEv < 32 by decide), hs₉.ld (d := 8 * kEv) (by unfold kEv sFn; omega_arith), hev₉]
    rw [BitVec.toNat_not, show (BitVec.setWidth 64 1#16 : BitVec 64).toNat = 1 from rfl, Bool.toNat_true,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hte]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    omega_arith)
    (by decide) (by decide) (by decide +kernel)) fun s₁₀ ⟨⟨c₁₀, m₁₀⟩, k₁₀⟩ => ?_
  obtain h10₁₀ := (k₁₀.gpr .x10 (by decide)).trans h10₉
  obtain h7₁₀ := (((k₈.trans k₉).trans k₁₀).gpr .x7 (by decide)).trans h7₇
  obtain h0₁₀ : s₁₀.gpr .x0 = I.B := (k₁₀.gpr .x0 (by decide)).trans h0₉
  obtain hs₁₀ := hs₉.congr k₁₀.wr
  obtain hexp : (decide (e % 2 = 1) && decide (3 ≤ e) && decide (e < 2 ^ 33)) = Spec.Rsa.exponentValid e := by
    unfold Spec.Rsa.exponentValid
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  obtain hfin : (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) &&
      decide (e % 2 = 1) && decide (3 ≤ e) && decide (e < 2 ^ 33)) = finalOk I.W n P Q e ok := by
    simp only [finalOk, ← hexp, Bool.and_assoc]
  refine WP.mono (WP.keep [.x4, .x10, .x15] (Q := fun t => t.mem = s₁₀.mem.writeW (off I.B (8 * kOk))
      (mask (finalOk I.W n P Q e ok))) (by
    brun [borrowMask, finSt, h7₁₀, h10₁₀, c₁₀, h0₁₀, hdr_enc (show kOk < 32 by decide),
      hs₁₀.st (d := 8 * kOk) (by unfold kOk sFn; omega_arith)]
    rw [show (0 : BitVec 64) - 1#64 = mask true from rfl, show (0 : BitVec 64) = mask false from rfl, ite_mask_not_k,
      mask_and', hfin])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨mt, kt⟩ => ?_
  obtain hm₁₀ : s₁₀.mem = s₅.mem := by rw [m₁₀, m₉, m₈, m₇, m₆]
  rw [hm₁₀] at mt
  obtain ⟨ht, ft, okt⟩ := h₅.hdrW (i := kOk) (by unfold kOk sFn; omega_arith) mt
    (((((k₆.trans k₇).trans k₈).trans k₉).trans k₁₀).trans kt)
  exact ⟨ht, by rw [← hm₅]; exact ft, okt⟩

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-!
# An RSA key from its primes on AArch64: constant time, `keyPart`

`qInv`, `dP`, `dQ`, `n` and the final mask, from the front's facts and a
mask in `kOk` (`TF`), which each keeps (`qinvPart_ct`, `crtPart_ct`,
`nPart_ct`, `finalMask_ct`); then the stores and the exit (`keyPart_ct`).
Each is a chain checked by the taint analysis, with the facts between its
parts from their correctness, and the facts after it from the correctness
of the whole (`qinvPart_k`, `crtPart_k`, `nPart_k`, `finalMask_k`).

`finalMask` reloads `w` and the stride twice in its middle: its three
parts are checked one after the other, with `KS` between them from the
correctness of the first (`finTopT_k`) and of the second (`finOddT_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- Before and after each piece of `keyPart`: the front's facts and a mask
in `kOk`. -/
abbrev TF : KIn → State → Prop := fun I t => PF I t ∧ KokM I t

/-! ## Shared pieces -/

theorem gcdIsOneT_eq : gcdIsOne = constA 1 ++ (eqMask aV aC ++
    ([.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3, sth .x15 kOk]] : List (Prog isa))) := by
  simp only [gcdIsOne, List.append_assoc]

/-- `gcdIsOne`, with no postcondition. -/
theorem gcdIsOneT_ct0 {F : KIn → State → Prop} : RelCT isa (Two (KG F)) (seqs gcdIsOne) fun _ _ => True := by
  rw [gcdIsOneT_eq]
  refine rs_app (R := Two (KG NF)) (by simp [constA]) (by simp [eqMask, eqA])
    ((constA_ct 1 (by decide) (stab_nf _ _) (by taint_decide) (by taint_decide)).mono
      (fun _ _ h => two_kg (fun _ _ _ => trivial) h) fun _ _ h => h) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := NF) (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) (by taint_decide)) ?_
  exact (two_taint [.x0] (pins_kg NF) (by taint_decide) :
    RelCT isa _ (.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3, sth .x15 kOk]) fun _ _ => True)

theorem divisorOfT_eq (j : Nat) : divisorOf j = [zeroA aM, copyA aM j] ++ (constA 0 ++ (eqMask j aC ++
    ([.block (ws ++ (base aM .x16 ++ ([ld .x3 .x16, movi .x4 1, .logic .and .x .x4 .x15 .x4,
      .logic .orr .x .x3 .x3 .x4, st .x3 .x16] : List Instr)))] : List (Prog isa)))) := by
  simp only [divisorOf, List.append_assoc]

/-- `divisorOf j` (the taint checks of the code that depends on `j` as
parameters). -/
theorem divisorOfT_ct {j : Nat} (hj : j < 16) (hjM : j ≠ aM) (hjC : j ≠ aC)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x16 ++ base aM .x17)) copyWords)
      hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x9 0, mov .x14 .x12] : List Instr))
      (.seq (.block (base j .x16 ++ base aC .x17)) (.seq (countLoop .x14 xorBody) (.block zeroMask)))) hc₂).isSome =
      true) :
    RelCT isa (Two (KG NF)) (seqs (divisorOf j)) (Two (KG NF)) := by
  refine kg_ct ?_ fun I _ s h _ _ => WP.mono (divisorOf_k h hj hjM hjC) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩
  rw [divisorOfT_eq]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aM, copyA aM j]) _ from
    RelCT.seq (zeroA_ct (by decide) (stab_nf _ _) (by taint_decide)) (copyA_ct (by decide) hj hjM.symm
      (stab_nf _ _) ht₁)) ?_
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 0 (by decide) (stab_nf _ _) (by taint_decide)
    (by taint_decide)) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := NF) hj (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) ht₂) ?_
  exact (kg_wsb0 (by taint_decide) : RelCT isa _ (.block (ws ++ (base aM .x16 ++ ([ld .x3 .x16, movi .x4 1,
    .logic .and .x .x4 .x15 .x4, .logic .orr .x .x3 .x3 .x4, st .x3 .x16] : List Instr)))) fun _ _ => True)

/-! ## `qInv` -/

/-- `KokM` and word `W` of `u` zero, across a piece that keeps memory. -/
theorem kt_mem {I : KIn} {s t : State} (hm : t.mem = s.mem) (h : KokM I s ∧ TopZ aU I s) :
    KokM I t ∧ TopZ aU I t := by
  obtain ⟨⟨c, hc⟩, ht⟩ := h
  refine ⟨⟨c, ?_⟩, ?_⟩
  · dsimp only [word] at hc ⊢; rw [hm]; exact hc
  · dsimp only [TopZ, atop, word] at ht ⊢; rw [hm]; exact ht

/-- `qinvPart`'s mask block. -/
abbrev qBlkT : List Instr :=
  ([mov .x10 .x15] : List Instr) ++ (evenMaskOf aPa ++ ([.logic .orr .x .x15 .x15 .x10] : List Instr))

theorem qinvBlk_eq : ([mov .x10 .x15] : List Instr) ++ (evenMaskOf aPa ++ ([.logic .orr .x .x15 .x15 .x10] :
    List Instr)) = ([mov .x10 .x15] : List Instr) ++ (ws ++ (base aPa .x16 ++ (([ld .x3 .x16, movi .x4 1,
      .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr) ++
      ([.logic .orr .x .x15 .x15 .x10] : List Instr)))) := by
  simp only [evenMaskOf, List.append_assoc]

/-- The mask block: memory kept, a mask in `x15`. -/
theorem qinvBlkT_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {c : Bool} (h15 : s.gpr .x15 = mask c) :
    WP isa (.block qBlkT) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧ X15M I t := by
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x10]
    (Q := fun t => t.gpr .x10 = mask c ∧ t.mem = s.mem) (by brun [h15]) (by decide) (by decide)
      (by decide +kernel)) fun s₄ ⟨⟨h10₄, m₄⟩, k₄⟩ => WP.block_append_iff.mpr ?_)
  have h₄ := h.regs m₄ k₄
  refine WP.mono (evenMaskOf_k h₄ (j := aPa) (by decide)) fun s₅ ⟨h₅, m₅, h15₅, _, _, k₅⟩ => ?_
  have h10₅ : s₅.gpr .x10 = mask c := by rw [k₅.gpr .x10 (by decide), h10₄]
  refine WP.mono (WP.keep [.x15] (Q := fun t => t.gpr .x15 = mask (decide (av I s₄.mem aPa % 2 = 0) || c) ∧
    t.mem = s₅.mem) (by brun [h15₅, h10₅, qinv_mask_or]) (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨⟨h15₆, m₆⟩, k₆⟩ => ⟨h₅.regs m₆ k₆, by rw [m₆, m₅, m₄], _, h15₆⟩

/-- The mask block, keeping `KokM` and word `W` of `u` zero. -/
theorem qinvBlkT_ct : RelCT isa (Two (KG fun I t => (KokM I t ∧ TopZ aU I t) ∧ X15M I t)) (.block qBlkT)
    (Two (KG fun I t => (KokM I t ∧ TopZ aU I t) ∧ X15M I t)) := by
  refine kg_ct ?_ fun I _ s h _ ⟨hf, _, h15⟩ => WP.mono (qinvBlkT_k h h15) fun t ⟨ht, hm, hx⟩ =>
    ⟨ht, kt_mem hm hf, hx⟩
  show RelCT isa _ (.block (([mov .x10 .x15] : List Instr) ++ (evenMaskOf aPa ++
    ([.logic .orr .x .x15 .x15 .x10] : List Instr)))) _
  rw [qinvBlk_eq]
  exact kg_blk_ws0 (G := NF) (by taint_decide) (fun I _ s h _ _ => WP.mono (WP.keep [.x10] (Q := fun t => t.mem = s.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun _ ⟨hm, k⟩ => ⟨h.regs hm k, trivial⟩)
    (by taint_decide)

/-- `qinvPre`, with no postcondition, from a mask in `kOk`. -/
theorem qinvPreT_ct0 : RelCT isa (Two (KG KokM)) (seqs qinvPre) fun _ _ => True := by
  have sK : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .hdr kOk ∉ cs → Stab KokM cs rs :=
    fun _ rs hok hn => stab_kok rs hok hn
  have sT : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .arr aU ∉ cs → Stab (TopZ aU) cs rs :=
    fun _ rs hok hn => stab_top rs (by decide) hok hn
  unfold qinvPre
  -- `[aU] := q`, word `W` zero.
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aU, copyA aU aQa]) _ from
    zc_ct (by decide) (by decide) (by decide) (sK _ _ (by decide) (by decide)) (by taint_decide)
      (by taint_decide)) ?_
  -- `x15 := ` the mask of `p < 3`.
  refine rs_app (by simp [constA]) (by simp [ltA, cmpA]) (constA_ct 3 (by decide)
    (stab_and (sK _ _ (by decide) (by decide)) (sT _ _ (by decide) (by decide))) (by taint_decide)
    (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => (KokM I t ∧ TopZ aU I t) ∧ X15M I t)) (by simp [ltA, cmpA]) (by simp)
    (ltA_ct (by decide) (by decide) (fun _ _ _ _ hf hm _ h15 => ⟨kt_mem hm hf, _, h15⟩) (by taint_decide)) ?_
  -- The mask of `p` even or below 3; `[aM] := p`.
  refine rs_app (R := Two (KG fun I t => (KokM I t ∧ TopZ aU I t) ∧ X15M I t)) (by simp) (by simp [selC]) ?_ ?_
  · have sX : ∀ (rs : List Reg), .x15 ∉ rs →
        Stab (fun I t => (KokM I t ∧ TopZ aU I t) ∧ X15M I t) [.arr aM] rs := fun _ h =>
      stab_and (stab_and (sK _ _ (by decide) (by decide)) (sT _ _ (by decide) (by decide))) (stab_x15 h)
    exact RelCT.seq qinvBlkT_ct (RelCT.seq (zeroA_ct (by decide) (sX _ (by decide)) (by taint_decide))
      (copyA_ct (by decide) (by decide) (by decide) (sX _ (by decide)) (by taint_decide)))
  -- `[aM] := M`.
  refine rs_app (by simp [selC]) (by simp [invFrom]) (selC_ct (F := fun I t => KokM I t ∧ TopZ aU I t)
    (by decide) (by decide) (stab_and (sK _ _ (by decide) (by decide)) (sT _ _ (by decide) (by decide)))
    (by taint_decide)) ?_
  -- `[aV] := [aM]`.
  exact (show RelCT isa _ (seqs (([zeroA aV] : List (Prog isa)) ++ ([copyA aV aM, zeroA aX₁, .block (setOneA aX₁),
      zeroA aX₂] : List (Prog isa)))) _ from
    rs_app (by simp) (by simp) (zeroA_ct (by decide)
      (stab_and (sK [.arr aV] _ (by decide) (by decide)) (sT [.arr aV] _ (by decide) (by decide)))
      (by taint_decide))
      (invStart_ct (o := aV) (a := aM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (stab_and (sK [.arr aV, .arr aX₁, .arr aX₂] _ (by decide) (by decide))
          (sT [.arr aV, .arr aX₁, .arr aX₂] _ (by decide) (by decide))) (by taint_decide))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-- `qinvPart`, with no postcondition, from `TF`: the inverse at the
primes' width, from `qinvPre_k`'s `[aU] = q` and `[aV] = [aM] = qMod p`. -/
theorem qinvPartT_ct0 [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG TF)) (seqs qinvPart) fun _ _ => True := by
  have sK : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .hdr kOk ∉ cs → Stab KokM cs rs :=
    fun _ rs hok hn => stab_kok rs hok hn
  rw [qinvPart_eq]
  refine rs_app (R := Two (KG fun I t => KokM I t ∧ AvEq aV aM I t ∧ Fits aU I t ∧ Fits aM I t))
    (by simp [qinvPre]) (by simp)
    (kg_ct (qinvPreT_ct0.mono (fun _ _ h => two_kg (fun _ _ h => h.2) h) fun _ _ h => h)
      fun I _ s h L ⟨hf, c, hok⟩ => WP.mono (qinvPre_k h hf.1 hf.2.1) fun t ⟨ht, f, vU, vV, vM⟩ =>
        ⟨ht, ⟨c, (f.word (by decide) (by decide) (by decide)).trans hok⟩, by dsimp only [AvEq]; rw [vV, vM],
          by dsimp only [Fits]; rw [vU]; exact L.Q_lt,
          by dsimp only [Fits]; rw [vM]; exact qMod_lt L.P_lt (by have := L.pl1; omega_arith)⟩) ?_
  refine rs_app (R := Two (KG KokM)) (by simp) (by simp [gcdIsOne, constA])
    (show RelCT isa _ (seqs [inverseAt halfW aU aV aX₁ aX₂ aM aT]) _ from
    inverseHalf_ct (F := KokM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (sK _ _ (by decide) (by decide))
    (by taint_decide)) gcdIsOneT_ct0

/-- `qinvPart` keeps `TF`. -/
theorem qinvPart_ct [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG TF)) (seqs qinvPart) (Two (KG TF)) :=
  kg_ct qinvPartT_ct0
    fun I _ s h L ⟨hf, _, hok⟩ => WP.mono (qinvPart_k h L hf.1 hf.2.1 L.P_lt L.Q_lt hok) fun _ ⟨ht, f, ok, _⟩ =>
      ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f, _, ok⟩

/-! ## `dP`, `dQ` and `n` -/

theorem crtPartT_eq : crtPart = divisorOf aPm ++ (([zeroA aU, copyA aU aDd, divmod aU aV aM aT, zeroA aX₁,
    copyA aX₁ aV] : List (Prog isa)) ++ (divisorOf aQm ++ ([zeroA aU, copyA aU aDd, divmod aU aV aM aT] :
      List (Prog isa)))) := by
  simp only [crtPart, List.append_assoc]

/-- `crtPart`, with no postcondition. -/
theorem crtPartT_ct0 : RelCT isa (Two (KG NF)) (seqs crtPart) fun _ _ => True := by
  have tail : RelCT isa (Two (KG NF)) (seqs [zeroA aU, copyA aU aDd, divmod aU aV aM aT]) (Two (KG NF)) :=
    RelCT.seq (zeroA_ct (by decide) (stab_nf _ _) (by taint_decide))
      (RelCT.seq (copyA_ct (by decide) (by decide) (by decide) (stab_nf _ _) (by taint_decide))
        (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (stab_nf _ _) (by taint_decide) (by taint_decide)))
  rw [crtPartT_eq]
  refine rs_app (by simp [divisorOf]) (by simp) (divisorOfT_ct (j := aPm) (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [divisorOf]) (show RelCT isa _ (seqs (([zeroA aU, copyA aU aDd,
    divmod aU aV aM aT] : List (Prog isa)) ++ ([zeroA aX₁, copyA aX₁ aV] : List (Prog isa)))) _ from
      rs_app (by simp) (by simp) tail (RelCT.seq (zeroA_ct (by decide) (stab_nf _ _) (by taint_decide))
        (copyA_ct (by decide) (by decide) (by decide) (stab_nf _ _) (by taint_decide)))) ?_
  exact RelCT.drop (rs_app (by simp [divisorOf]) (by simp) (divisorOfT_ct (j := aQm) (by decide) (by decide)
    (by decide) (by taint_decide) (by taint_decide)) tail)

/-- `crtPart` keeps `TF`. -/
theorem crtPart_ct : RelCT isa (Two (KG TF)) (seqs crtPart) (Two (KG TF)) :=
  kg_ct (crtPartT_ct0.mono (fun _ _ h => two_kg (fun _ _ _ => trivial) h) fun _ _ h => h)
    fun I _ s h _ ⟨hf, c, hok⟩ => WP.mono (crtPart_k h rfl rfl rfl) fun _ ⟨ht, f, _⟩ =>
      ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f, c,
        (f.word (by decide) (by decide) (by decide)).trans hok⟩

/-- `nPart` keeps `TF`. -/
theorem nPart_ct : RelCT isa (Two (KG TF)) (seqs nPart) (Two (KG TF)) :=
  kg_ct (mulTo_ct0 (by decide) (by taint_decide) (by taint_decide)) fun I _ s h L ⟨hf, c, hok⟩ =>
    WP.mono (nPart_k h L.W hf.1 hf.2.1 L.P_lt L.Q_lt) fun _ ⟨ht, f, _⟩ =>
      ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f, c,
        (f.word (by decide) (by decide) (by decide)).trans hok⟩

/-! ## The final mask -/

theorem finalMask_eq3 : finalMask = (ws ++ (base aQt .x16 ++ finTop)) ++ ((ws ++ (base aPa .x16 ++
    (([movi .x7 0, ld .x3 .x16] : List Instr) ++ (oddMask ++ finAnd)))) ++ (ws ++ (base aQa .x16 ++
    (([movi .x7 0, ld .x3 .x16] : List Instr) ++ (oddMask ++ (finAnd ++ (finE1 ++ (finE2 ++ ((carryMask ++ finAnd) ++
    (finE3 ++ (borrowMask ++ finSt))))))))))) := by
  rw [finalMask_eq]; simp only [oddMaskOf, List.append_assoc, List.cons_append, List.nil_append]

/-- `finalMask`'s first part: memory kept, registers of `mmRegs` changed. -/
theorem finTopT_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aQt .x16 ++ finTop))) s (KS I s₀) := by
  have hnw := h.ws.scr.nowrap
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_using [this]
  have hw2 := h.ws.w2
  have sN := h.ws.sl (j := aQt) (by decide)
  have h256 := h.ws.h256
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h aQt) fun s₁ ⟨⟨h16, h12, _, m₁⟩, k₁⟩ => ?_
  have hs₁ := h.ws.scr.congr k₁.wr
  have h0₁ : s₁.gpr .x0 = I.B := (k₁.gpr .x0 (by decide)).trans h.ws.x0
  refine WP.mono (WP.keep [.x3, .x7, .x10, .x16] (Q := fun t => t.mem = s.mem) (by
    brun [finTop, h16, h12, h0₁, m₁, top_addr I.B (d := slot I.W aQt) (w := I.W) hw1 (by omega_using [hw2]),
      hs₁.ld (d := slot I.W aQt + 8 * (I.W - 1)) (by omega_using [sN]), hdr_enc (show kOk < 32 by decide),
      hs₁.ld (d := 8 * kOk) (by unfold kOk sFn; omega_using [h256])])
    (by decide) (by decide) (by decide +kernel)) fun _ ⟨hm, k⟩ => h.regs hm (k₁.trans k)

/-- `finalMask`'s second part: memory kept, registers of `mmRegs` changed. -/
theorem finOddT_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aPa .x16 ++ (([movi .x7 0, ld .x3 .x16] : List Instr) ++ (oddMask ++ finAnd)))))
      s (KS I s₀) := by
  have e : ws ++ (base aPa .x16 ++ (([movi .x7 0, ld .x3 .x16] : List Instr) ++ (oddMask ++ finAnd))) =
      oddMaskOf aPa ++ finAnd := by
    simp only [oddMaskOf, List.append_assoc]
  rw [e]
  refine WP.block_append_iff.mpr (WP.mono (oddMaskOf_k h (j := aPa) (by decide)) fun s₃ ⟨h₃, _⟩ => ?_)
  exact WP.mono (WP.keep [.x10] (Q := fun t => t.mem = s₃.mem) (by brun [finAnd]) (by decide) (by decide)
    (by decide +kernel)) fun _ ⟨hm, k⟩ => h₃.regs hm k

/-- `finalMask` keeps `TF`. -/
theorem finalMask_ct : RelCT isa (Two (KG TF)) (.block finalMask) (Two (KG TF)) := by
  refine kg_ct ?_ fun I _ s h L ⟨hf, _, hok⟩ =>
    WP.mono (finalMask_k h rfl hf.1 hf.2.1 L.E_lt hf.2.2.2.2.1 hok) fun _ ⟨ht, f, ok⟩ =>
      ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f, _, ok⟩
  rw [finalMask_eq3]
  exact RelCT.block_append (RelCT.seq
    (kg_ct (G := NF) (kg_wsb0 (by taint_decide)) fun I _ s h _ _ => WP.mono (finTopT_k h) fun _ ht => ⟨ht, trivial⟩)
    (RelCT.block_append (RelCT.seq
      (kg_ct (G := NF) (kg_wsb0 (by taint_decide)) fun I _ s h _ _ => WP.mono (finOddT_k h) fun _ ht =>
        ⟨ht, trivial⟩)
      (kg_wsb0 (by taint_decide)))))

/-! ## `keyPart` -/

theorem keyPart_ct [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG TF)) keyPart fun _ _ => True := by
  rw [keyPart]
  simp only [List.append_assoc]
  refine rs_app (by simp [qinvPart]) (by simp [crtPart, divisorOf]) qinvPart_ct ?_
  refine rs_app (by simp [crtPart, divisorOf]) (by simp [nPart]) crtPart_ct ?_
  refine rs_app (by simp [nPart, mulTo]) (by simp) nPart_ct ?_
  refine rs_app (by simp) (by simp [outputs, storeA]) finalMask_ct ?_
  exact outputs_ct.mono (fun _ _ ⟨p, ⟨I₁, _, e₁, _, k₁, L₁, O₁, _, m₁⟩, ⟨I₂, _, e₂, _, k₂, L₂, O₂, _, m₂⟩, hsp⟩ =>
    ⟨p, ⟨I₁, e₁, k₁.ws, k₁.args, k₁.wr, L₁, O₁, m₁⟩, ⟨I₂, e₂, k₂.ws, k₂.args, k₂.wr, L₂, O₂, m₂⟩, hsp⟩)
    fun _ _ h => h

end VG.Proof.RsaKeyGen.AArch64.Key
