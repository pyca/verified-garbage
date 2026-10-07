import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Ctx
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail

/-!
# An RSA key from its primes on AArch64: the outputs

The arrays, masked by `kOk`, to their outputs (`stores_ok`, for any list of
stores to outputs apart from each other), `kOk`'s low bit returned
(`keyExit_ok`), and zeros to the outputs (`zeros_ok`).
-/

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
  hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)

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
      (fun t ht ft bt xt kt => k t ht (Frm.trans f₁ ft) ?_ ?_ ((k₁.trans kt).mono (by simp)))
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
        rw [f₁.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)]
    · intro x hx
      rw [xt x fun e' he' => hx e' (List.mem_cons_of_mem _ he'), x₁ x (hx e List.mem_cons_self)]

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
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
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
    have hz := zeroOut_ok h.scr h.x0 h256 hp hl hpv hlv hl1 (by have := h.w2; omega) ⟨hwr, hsep⟩
    have step : ∀ s₁, ((∀ i < e.len, s₁.mem (e.out + BitVec.ofNat 64 i) = 0) ∧
        (∀ x, (∀ j < e.len, x ≠ e.out + BitVec.ofNat 64 j) → s₁.mem x = s.mem x) ∧ Keep [.x1, .x2, .x3] s s₁) →
        WP isa (seqs (zerosK L ++ rest)) s₁ Q := by
      intro s₁ ⟨z₁, x₁, k₁⟩
      have f₁ := frm_scr hsep x₁
      have h₁ : Ws s₁ B Z w := h.congr f₁ (fun r hr' => by
        rw [List.mem_singleton.mp hr']; exact Or.inl (by omega)) k₁ (by decide)
      refine zeros_ok L rest s₁ hr h₁ (fun e' he' => (ho e' (List.mem_cons_of_mem _ he')).congr f₁ h256 k₁.wr)
        hpw'.2 (fun t ht ft zt xt kt => k t ht (Frm.trans f₁ ft) ?_ ?_ ((k₁.trans kt).mono (by simp)))
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
