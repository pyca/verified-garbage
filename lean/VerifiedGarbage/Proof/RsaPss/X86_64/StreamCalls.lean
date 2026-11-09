module

-- separate module: its proofs build in parallel with `TabCall`'s and `Loops`'s, which `Mgf` also imports

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.RsaPss.X86_64.CtHash
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86-64: calling the streaming hash functions

As RSAES-OAEP's (`Proof/RsaOaep/X86_64/Hash.lean`), for the frame of
`encode` and `checkEncoding`: the streaming `init`, `update` and `finalize`
of a hash function (a `StreamOK`, `Proof/Pbkdf2/Md/X86_64/Calls.lean`),
called from the frame on the state at `scratch + oSt`, with the working
space at `scratch + oCW` (below the state) and the digest to `scratch + o`
(above it): what each leaves of the frame and the working space (`Lay`,
`Rep`, with the ranges it writes read again), and what it computes; and
that each is constant time in two runs whose arguments agree (`two_init`,
`two_upd`, `two_fin`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off word off_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK After init_call upd_call fin_call UpdArgs FinArgs)
open VG.Proof.Bignum.X86_64 (Two)

variable {G : Stream} (hG : StreamOK G)

include hG in
theorem sizes : G.S ≤ 256 ∧ G.F ≤ 64 ∧ hG.Wb ≤ 2048 ∧ G.D ≤ G.F ∧ 0 < G.D :=
  ⟨hG.hSB, hG.hF, by have := hG.hWb; have := hG.hW; omega, hG.hDF, hG.hD0⟩

/-- A range of our working space and the 16 bytes below the frame are
apart. -/
theorem Lay.stk {t : State} {F S : Addr} (L : Lay t F S) {o n : Nat} (h : o + n ≤ oRsa) :
    (below (t.gpr .rsp) 16).Disjoint ⟨off S o, n⟩ := by
  rw [L.rsp]; exact L.dRS.sub_right (Offset.sub_base S h)

/-- Two ranges of our working space that do not overlap. -/
theorem sdis (S : Addr) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ oRsa) (hb : b + k ≤ oRsa) :
    Region.Disjoint ⟨off S a, n⟩ ⟨off S b, k⟩ :=
  Offset.disjoint S h (by unfold oRsa at ha; omega) (by unfold oRsa at hb; omega)

/-- After a call that keeps `rsp` and the callee-saved registers. -/
theorem keep_rsp {t t' : State} (h : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : t'.gpr .rsp = t.gpr .rsp :=
  h .rsp (by decide)

/-! ## `init` -/

include hG in
theorem init_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (hdi : t.gpr .rdi = off S oSt) :
    WP isa (.call G.initN G.initC) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S)] o then t'.mem (off S o) else V o) W ∧
      Frame (regs S [(oSt, G.S)] ++ [retR F]) t.mem t'.mem ∧
      hG.SH.Repr t'.mem (off S oSt) [] := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  refine init_call hG hdi (L.cov h1) (L.stk h1) fun t' A hr => ?_
  have hF : Frame (regs S [(oSt, G.S)] ++ [retR F]) t.mem t'.mem := by
    have := A.frame; rw [L.rsp] at this; exact this
  obtain ⟨L', R'⟩ := L.after_call R (rgs := [(oSt, G.S)])
    (by simp only [List.mem_singleton]; rintro p rfl; exact h1) hF (keep_rsp A.cs) A.wr
  exact ⟨L', A.rd, A.wr, A.cs, R', hF, hr⟩

/-! ## `update` -/

include hG in
/-- The arguments of `update` of the state with the `len` bytes at
`scratch + a`. -/
theorem updArgs {t : State} {F S : Addr} (L : Lay t F S) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + G.S ≤ a) (hwa : a + len ≤ oCW ∨ oCW + hG.Wb ≤ a)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S a) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oCW) : UpdArgs hG t (off S oSt) (off S a) (off S oCW) len := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oCW + hG.Wb ≤ oRsa := by unfold oCW oRsa; omega
  have hws : oCW + hG.Wb ≤ oSt := by unfold oSt oCW; omega
  exact { rdi := hdi, rdx := hdx
          rcx := by rw [hcx, BitVec.toNat_ofNat]; unfold oRsa at ha; omega
          r8 := h8
          cd := Covers.right (L.cov ha)
          cw := Covers.pair (L.cov h1) (L.cov h2)
          st_sc := sdis S (Or.inr hws) h1 h2
          d_st := sdis S hda ha h1
          d_sc := sdis S hwa ha h2
          stk_st := L.stk h1, stk_d := L.stk ha, stk_sc := L.stk h2 }

include hG in
/-- `update` of the state with the `len` bytes at `scratch + a`, after
`cnt` bytes, from the arguments in `rdi`, `rsi`, `rdx`, `rcx`, `r8`. -/
theorem upd_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + G.S ≤ a) (hwa : a + len ≤ oCW ∨ oCW + hG.Wb ≤ a)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S a) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oCW) :
    WP isa (.call G.updN G.updC) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S), (oCW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .rsi = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ (List.range len).map fun i => V (a + i))) := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oCW + hG.Wb ≤ oRsa := by unfold oCW oRsa; omega
  have hws : oCW + hG.Wb ≤ oSt := by unfold oSt oCW; omega
  have args := updArgs hG L ha hda hwa hdi hdx hcx h8
  refine upd_call hG args (by unfold oRsa at ha; omega) fun t' A hr => ?_
  obtain ⟨L', R'⟩ := L.after_call R (rgs := [(oSt, G.S), (oCW, hG.Wb)])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl) <;> with_reducible assumption)
    (by have := A.frame; rw [L.rsp] at this; exact this) (keep_rsp A.cs) A.wr
  refine ⟨L', A.rd, A.wr, A.cs, R', fun m hm hc => ?_⟩
  have e : Spec.Sha256.bytesAt t.mem (off S a) len = (List.range len).map fun i => V (a + i) := by
    simp only [Spec.Sha256.bytesAt]
    exact List.map_congr_left fun i hi => by
      rw [off_plus]; exact R.scr _ (by have := List.mem_range.mp hi; omega)
  rw [← e]; exact hr m hm hc

/-! ## `finalize` -/

include hG in
/-- The arguments of `finalize` of the state to `scratch + o`. -/
theorem finArgs {t : State} {F S : Addr} (L : Lay t F S) {o : Nat} (ho : oSt + 256 ≤ o ∧ o + 64 ≤ oRsa)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S o) (hcx : t.gpr .rcx = off S oCW) :
    FinArgs hG t (off S oSt) (off S o) (off S oCW) := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oCW + hG.Wb ≤ oRsa := by unfold oCW oRsa; omega
  have h3 : o + G.F ≤ oRsa := by unfold oSt oCW oRsa at *; omega
  have hws : oCW + hG.Wb ≤ oSt := by unfold oSt oCW; omega
  exact { rdi := hdi, rdx := hdx, rcx := hcx
          cw := Covers.cons (L.cov h1) (Covers.pair (L.cov h3) (L.cov h2))
          st_o := sdis S (by unfold oSt oCW at *; omega) h1 h3
          st_sc := sdis S (Or.inr hws) h1 h2
          o_sc := sdis S (by unfold oSt oCW at *; omega) h3 h2
          stk_st := L.stk h1, stk_o := L.stk h3, stk_sc := L.stk h2 }

include hG in
/-- `finalize` of the state to `scratch + o`, from the arguments in `rdi`,
`rsi`, `rdx`, `rcx`. -/
theorem fin_frame_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {o : Nat} (ho : oSt + 256 ≤ o ∧ o + 64 ≤ oRsa)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S o) (hcx : t.gpr .rcx = off S oCW) :
    WP isa (.call G.finN G.finC) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun x => if inR [(oSt, G.S), (o, G.F), (oCW, hG.Wb)] x then t'.mem (off S x) else V x) W ∧
      Frame (regs S [(oSt, G.S), (o, G.F), (oCW, hG.Wb)] ++ [retR F]) t.mem t'.mem ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → m.length < 2 ^ 64 → t.gpr .rsi = BitVec.ofNat 64 m.length →
        ∀ i < G.D, t'.mem (off S (o + i)) = (hG.SH.H.hash m).getD i 0) := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oCW + hG.Wb ≤ oRsa := by unfold oCW oRsa; omega
  have h3 : o + G.F ≤ oRsa := by unfold oSt oCW oRsa at *; omega
  have hws : oCW + hG.Wb ≤ oSt := by unfold oSt oCW; omega
  have args := finArgs hG L ho hdi hdx hcx
  refine fin_call hG args fun t' A hr => ?_
  obtain ⟨L', R'⟩ := L.after_call R (rgs := [(oSt, G.S), (o, G.F), (oCW, hG.Wb)])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
    (by have := A.frame; rw [L.rsp] at this; exact this) (keep_rsp A.cs) A.wr
  refine ⟨L', A.rd, A.wr, A.cs, R', (by have hf := A.frame; rw [L.rsp] at hf; exact hf), fun m hm hl hc i hi => ?_⟩
  have e := hr m hm hl hc
  rw [← e, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  simp only [Spec.Sha256.bytesAt, List.getElem?_map, List.getElem?_range (show i < G.F by omega),
    Option.map_some, Option.getD_some, off_off]

include hG in
theorem fin_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {o : Nat} (ho : oSt + 256 ≤ o ∧ o + 64 ≤ oRsa)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S o) (hcx : t.gpr .rcx = off S oCW) :
    WP isa (.call G.finN G.finC) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun x => if inR [(oSt, G.S), (o, G.F), (oCW, hG.Wb)] x then t'.mem (off S x) else V x) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → m.length < 2 ^ 64 → t.gpr .rsi = BitVec.ofNat 64 m.length →
        ∀ i < G.D, t'.mem (off S (o + i)) = (hG.SH.H.hash m).getD i 0) := by
  exact WP.mono (fin_frame_ok hG L R ho hdi hdx hcx)
    fun _ ⟨Lt, rd, wr, cs, Rt, _, hr⟩ => ⟨Lt, rd, wr, cs, Rt, hr⟩

/-! ## In two runs -/

variable {α : Type}

include hG in
/-- `init`, on the state at `scratch + oSt` in both runs. -/
theorem two_init {Φ : α → State → Prop} (F S : α → Addr)
    (h : ∀ a t, Φ a t → Lay t (F a) (S a) ∧ t.gpr .rdi = off (S a) oSt) :
    RelCT isa (Two Φ) (.call G.initN G.initC) fun _ _ => True := by
  have h1 : oSt + G.S ≤ oRsa := by have := (sizes hG).1; unfold oSt oRsa; omega
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Φ a t₁ ∧ Φ a t₂) fun a =>
    Pbkdf2.Md.X86_64.Calls.init_rel hG (st := off (S a) oSt) fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono
    (fun _ _ h => h) fun _ _ h => h
  obtain ⟨L₁, d₁⟩ := h a t₁ p₁
  obtain ⟨L₂, d₂⟩ := h a t₂ p₂
  exact ⟨d₁, d₂, L₁.cov h1, L₂.cov h1, L₁.stk h1, L₂.stk h1, by rw [L₁.rsp, L₂.rsp]⟩

include hG in
/-- `update` with the `len a` bytes at `scratch + o a`, after `cnt a`. -/
theorem two_upd {Φ : α → State → Prop} (F S : α → Addr) (o len : α → Nat) (cnt : α → BitVec 64)
    (h : ∀ a t, Φ a t → Lay t (F a) (S a) ∧ o a + len a ≤ oRsa ∧ (o a + len a ≤ oSt ∨ oSt + G.S ≤ o a) ∧
      (o a + len a ≤ oCW ∨ oCW + hG.Wb ≤ o a) ∧ t.gpr .rdi = off (S a) oSt ∧ t.gpr .rsi = cnt a ∧
      t.gpr .rdx = off (S a) (o a) ∧ t.gpr .rcx = BitVec.ofNat 64 (len a) ∧ t.gpr .r8 = off (S a) oCW) :
    RelCT isa (Two Φ) (.call G.updN G.updC) fun _ _ => True := by
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Φ a t₁ ∧ Φ a t₂) fun a =>
    Pbkdf2.Md.X86_64.Calls.upd_rel hG (st := off (S a) oSt) (d := off (S a) (o a)) (sc := off (S a) oCW)
      (len := len a) fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  obtain ⟨L₁, a₁, b₁, c₁, d₁, e₁, f₁, g₁, i₁⟩ := h a t₁ p₁
  obtain ⟨L₂, -, -, -, d₂, e₂, f₂, g₂, i₂⟩ := h a t₂ p₂
  exact ⟨updArgs hG L₁ a₁ b₁ c₁ d₁ f₁ g₁ i₁, updArgs hG L₂ a₁ b₁ c₁ d₂ f₂ g₂ i₂, e₁.trans e₂.symm,
    by rw [L₁.rsp, L₂.rsp]⟩

include hG in
/-- `finalize` to `scratch + o a`, after `cnt a`. -/
theorem two_fin {Φ : α → State → Prop} (F S : α → Addr) (o : α → Nat) (cnt : α → BitVec 64)
    (h : ∀ a t, Φ a t → Lay t (F a) (S a) ∧ (oSt + 256 ≤ o a ∧ o a + 64 ≤ oRsa) ∧
      t.gpr .rdi = off (S a) oSt ∧ t.gpr .rsi = cnt a ∧ t.gpr .rdx = off (S a) (o a) ∧
      t.gpr .rcx = off (S a) oCW) :
    RelCT isa (Two Φ) (.call G.finN G.finC) fun _ _ => True := by
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Φ a t₁ ∧ Φ a t₂) fun a =>
    Pbkdf2.Md.X86_64.Calls.fin_rel hG (st := off (S a) oSt) (o := off (S a) (o a)) (sc := off (S a) oCW)
      fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  obtain ⟨L₁, ho, d₁, e₁, x₁, c₁⟩ := h a t₁ p₁
  obtain ⟨L₂, -, d₂, e₂, x₂, c₂⟩ := h a t₂ p₂
  exact ⟨finArgs hG L₁ ho d₁ x₁ c₁, finArgs hG L₂ ho d₂ x₂ c₂, e₁.trans e₂.symm, by rw [L₁.rsp, L₂.rsp]⟩

end VG.Proof.RsaPss.X86_64
