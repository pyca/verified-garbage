module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
public import VerifiedGarbage.Proof.Framework.AArch64.Dispatch
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Mgf1
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-OAEP on AArch64: the hash function by its number

`Mgf1.hcall sel hs f` loads the number `k` of a hash function from the slot
`sel` and runs `f` of the `k`th of `hs` (`hcall_wp`), from a state that
differs from the one before only in `x16` and `x17` (`Same`), which every
call clobbers anyway: so a call's lemma, for the hash function `k` names,
holds of the dispatched call too (`dinit_ok`, `dupd_ok`, `dupdExt_ok`,
`dfin_ok`). `hs` has the eight hash functions MD5 to SHA-512/256, by
number, and `k` is one of 1 to 7 (`Num`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (cases hcall initC updC finC)
open VG.Impl.Pbkdf2.Md.AArch64 (Stream Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)

/-- `u` is `t` with other values in `x16` and `x17`. -/
structure Same (t u : State) : Prop where
  mem : u.mem = t.mem
  sp : u.sp = t.sp
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  v : u.v = t.v
  gpr : ∀ r, r ≠ .x16 → r ≠ .x17 → u.gpr r = t.gpr r

/-- `hs`'s hash function `k`, for `k` one of 1 to 7, is `G`. -/
structure Num (hs : List Hash) (k : Nat) (G : Hash) : Prop where
  len : hs.length = 8
  k1 : 1 ≤ k
  k7 : k ≤ 7
  get : hs[k]? = some G

theorem Same.step {t u : State} (h : Same t u) (F S : Addr) (ws : List Region) : Step F S ws t u :=
  Step.blk ws h.rd h.wr h.sp h.v (fun r hr _ => h.gpr r (by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) h.mem

theorem Same.lay {t u : State} {F S : Addr} (h : Same t u) (L : Lay t F S) : Lay u F S :=
  L.congr h.sp h.wr (by rw [h.mem])

/-- The cases' keys are 1 to 7, and `k`'s is `f G`. -/
theorem cases_keys {hs : List Hash} (hl : hs.length = 8) (f : Hash → Prog isa) :
    Dispatch.keys (cases hs f) = [1, 2, 3, 4, 5, 6, 7] := by
  match hs, hl with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem cases_mem {hs : List Hash} {k : Nat} {G : Hash} (h : Num hs k G) (f : Hash → Prog isa) :
    (k, f G) ∈ cases hs f := by
  obtain ⟨hl, h1, h7, hg⟩ := h
  match hs, hl with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
      omega
    all_goals
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      simp [cases]

theorem cases_eq {hs : List Hash} {k : Nat} {G : Hash} (h : Num hs k G) (f : Hash → Prog isa) {c : Prog isa}
    (hc : (k, c) ∈ cases hs f) : c = f G :=
  Proof.Dispatch.case_unique (by rw [cases_keys h.len]; decide) hc (cases_mem h f)

theorem cases_lt {hs : List Hash} (hl : hs.length = 8) (f : Hash → Prog isa) :
    ∀ k ∈ Dispatch.keys (cases hs f), k < 4096 := by
  rw [cases_keys hl]; decide

theorem cases_key {hs : List Hash} {k : Nat} {G : Hash} (h : Num hs k G) (f : Hash → Prog isa) :
    k ∈ Dispatch.keys (cases hs f) := by
  rw [cases_keys h.len]
  have := h.k1; have := h.k7
  simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

/-- The dispatch on the number in `x16`, from a state with `k` there. -/
theorem chain_wp {hs : List Hash} {k : Nat} {G : Hash} (h : Num hs k G) (f : Hash → Prog isa) {t : State}
    (h16 : t.gpr .x16 = BitVec.ofNat 64 k) {Q : State → Prop}
    (hQ : ∀ u, Same t u → WP isa (f G) u Q) : WP isa (Impl.Dispatch.AArch64.chain .x17 .x16 (cases hs f)) t Q := by
  have hk : (t.gpr .x16).toNat = k := by
    rw [h16, BitVec.toNat_ofNat]; have := h.k7; omega
  refine Proof.Dispatch.chain_wp (Proof.Dispatch.AArch64.tests .x17 .x16 (by decide)) (cases hs f)
    (cases_lt h.len f) (by show (t.gpr .x16).toNat ∈ _; rw [hk]; exact cases_key h f)
    (by rw [cases_keys h.len]; decide) fun c hc s' ⟨w, hw⟩ _ => ?_
  have hc' : (k, c) ∈ cases hs f := by
    have e : Proof.Dispatch.AArch64.sel .x16 t = k := hk
    rw [e] at hc; exact hc
  rw [cases_eq h f hc']
  subst hw
  exact hQ _ ⟨rfl, rfl, rfl, rfl, rfl, fun r _ h17 => RegUpd.gpr_write_of_ne _ _ _ h17⟩

/-- `f` of the hash function `k`, whose number is in the slot `sel`. -/
theorem hcall_wp {hs : List Hash} {k : Nat} {G : Hash} (h : Num hs k G) (f : Hash → Prog isa) {sel : Nat}
    (hsel : sel % 8 = 0 ∧ sel < 32768) {t : State} (hld : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 sel) 8)
    (hv : t.mem.read (t.sp + BitVec.ofNat 64 sel) 8 = BitVec.ofNat 64 k) {Q : State → Prop}
    (hQ : ∀ u, Same t u → WP isa (f G) u Q) : WP isa (hcall sel hs f) t Q := by
  refine WP.seq (WP.mono (Q := fun (u : State) => Same t u ∧ u.gpr .x16 = BitVec.ofNat 64 k) ?_
    fun (u : State) hu' => ?_)
  · oaep_run [hld, hv, hsel.1, hsel.2]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, fun r h16 _ => RegUpd.gpr_write_of_ne _ _ _ h16⟩, trivial⟩
  obtain ⟨hu, h16⟩ := hu'
  exact chain_wp h f h16 fun w hw => hQ w ⟨hw.mem.trans hu.mem, hw.sp.trans hu.sp, hw.rd.trans hu.rd,
      hw.wr.trans hu.wr, hw.v.trans hu.v, fun r a b => (hw.gpr r a b).trans (hu.gpr r a b)⟩

/-! ## The streaming functions, dispatched -/

/-- A slot of the frame holding the hash function's number. -/
structure SelAt (t : State) (F : Addr) (sel k : Nat) : Prop where
  al : sel % 8 = 0
  lt : sel + 8 ≤ frameBytes
  sp : t.sp = F
  ld : InRegions (t.rd ++ t.wr) (F + BitVec.ofNat 64 sel) 8
  v : t.mem.read (F + BitVec.ofNat 64 sel) 8 = BitVec.ofNat 64 k

theorem SelAt.of_lay {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {sel j k : Nat} (hj : sel = 8 * j) (hjn : j < nW) (hw : W j = BitVec.ofNat 64 k) :
    SelAt t F sel k :=
  ⟨by omega, by subst hj; unfold nW frameBytes at *; omega, L.sp, L.ld (by subst hj; unfold nW frameBytes at *; omega),
    by rw [← hw, ← R.fr j hjn, hj]; rfl⟩

theorem dcall_wp {hs : List Hash} {k : Nat} {G : Hash} (h : Num hs k G) (f : Hash → Prog isa) {sel : Nat}
    {t : State} {F : Addr} (A : SelAt t F sel k) {Q : State → Prop}
    (hQ : ∀ u, Same t u → WP isa (f G) u Q) : WP isa (hcall sel hs f) t Q :=
  hcall_wp h f ⟨A.al, by have := A.lt; unfold frameBytes at this; omega⟩ (by rw [A.sp]; exact A.ld)
    (by rw [A.sp]; exact A.v) hQ

variable {hs : List Hash} {k : Nat} {G : Hash} (h : Num hs k G) (hG : StreamOK G.stream)

include h hG in
theorem dinit_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {sel : Nat} (A : SelAt t F sel k) (h0 : t.gpr .x0 = off S oSt) (ws : List Region) :
    WP isa (hcall sel hs initC) t fun t' => Lay t' F S ∧ Step F S ws t t' ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.stream.S)] o then t'.mem (off S o) else V o) W ∧
      hG.SH.Repr t'.mem (off S oSt) [] :=
  dcall_wp h initC A fun u hu => WP.mono (init_ok hG (hu.lay L) (hu.mem ▸ R)
    ((hu.gpr .x0 (by decide) (by decide)).trans h0) ws) fun _ ⟨L', S', R', hr⟩ =>
      ⟨L', (hu.step F S ws).trans S', R', hr⟩

include h hG in
theorem dupd_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {sel : Nat} (A : SelAt t F sel k) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + G.stream.S ≤ a) (hwa : a + len ≤ oW ∨ oW + hG.Wb ≤ a)
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = off S a) (h3 : t.gpr .x3 = BitVec.ofNat 64 len)
    (h4 : t.gpr .x4 = off S oW) (ws : List Region) :
    WP isa (hcall sel hs updC) t fun t' => Lay t' F S ∧ Step F S ws t t' ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.stream.S), (oW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .x1 = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ (List.range len).map fun i => V (a + i))) :=
  dcall_wp h updC A fun u hu => WP.mono (upd_ok hG (hu.lay L) (hu.mem ▸ R) ha hda hwa
    ((hu.gpr .x0 (by decide) (by decide)).trans h0) ((hu.gpr .x2 (by decide) (by decide)).trans h2)
    ((hu.gpr .x3 (by decide) (by decide)).trans h3) ((hu.gpr .x4 (by decide) (by decide)).trans h4) ws)
    fun _ ⟨L', S', R', hr⟩ => ⟨L', (hu.step F S ws).trans S', R', fun m hm hc =>
      hr m (by rw [hu.mem]; exact hm) ((hu.gpr .x1 (by decide) (by decide)).trans hc)⟩

include h hG in
theorem dupdExt_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {sel : Nat} (A : SelAt t F sel k) {d : Addr} {len : Nat} (hlen : len < 2 ^ 64)
    (hcd : Covers [⟨d, len⟩] (t.rd ++ t.wr)) (hds : Region.Disjoint ⟨d, len⟩ ⟨S, oRsa⟩)
    (hdk : (below F 16).Disjoint ⟨d, len⟩)
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = d) (h3 : t.gpr .x3 = BitVec.ofNat 64 len)
    (h4 : t.gpr .x4 = off S oW) (ws : List Region) :
    WP isa (hcall sel hs updC) t fun t' => Lay t' F S ∧ Step F S ws t t' ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.stream.S), (oW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .x1 = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ Spec.Rsa.bytesAt t.mem d len)) :=
  dcall_wp h updC A fun u hu => WP.mono (updExt_ok hG (hu.lay L) (hu.mem ▸ R) hlen
    (by rw [hu.rd, hu.wr]; exact hcd) hds hdk
    ((hu.gpr .x0 (by decide) (by decide)).trans h0) ((hu.gpr .x2 (by decide) (by decide)).trans h2)
    ((hu.gpr .x3 (by decide) (by decide)).trans h3) ((hu.gpr .x4 (by decide) (by decide)).trans h4) ws)
    fun _ ⟨L', S', R', hr⟩ => ⟨L', (hu.step F S ws).trans S', R', fun m hm hc => by
      have := hr m (by rw [hu.mem]; exact hm) ((hu.gpr .x1 (by decide) (by decide)).trans hc)
      rwa [hu.mem] at this⟩

include h hG in
theorem dfin_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {sel : Nat} (A : SelAt t F sel k) {o : Nat}
    (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = off S o) (h3 : t.gpr .x3 = off S oW) (ws : List Region) :
    WP isa (hcall sel hs finC) t fun t' => Lay t' F S ∧ Step F S ws t t' ∧
      Rep t'.mem F S (fun x => if inR [(oSt, G.stream.S), (o, G.stream.F), (oW, hG.Wb)] x then t'.mem (off S x) else V x) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → m.length < 2 ^ 64 → t.gpr .x1 = BitVec.ofNat 64 m.length →
        ∀ i < G.stream.D, t'.mem (off S (o + i)) = (hG.SH.H.hash m).getD i 0) :=
  dcall_wp h finC A fun u hu => WP.mono (fin_ok hG (hu.lay L) (hu.mem ▸ R) ho
    ((hu.gpr .x0 (by decide) (by decide)).trans h0) ((hu.gpr .x2 (by decide) (by decide)).trans h2)
    ((hu.gpr .x3 (by decide) (by decide)).trans h3) ws)
    fun _ ⟨L', S', R', hr⟩ => ⟨L', (hu.step F S ws).trans S', R', fun m hm hl hc =>
      hr m (by rw [hu.mem]; exact hm) hl ((hu.gpr .x1 (by decide) (by decide)).trans hc)⟩

end VG.Proof.RsaOaep.AArch64
