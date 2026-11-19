module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

/-! ### `RsaOaep.X86_64.MgfCT`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.X86_64.CtBase`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP on x86-64: relating two runs

The constant-time proofs relate two runs piece by piece (`RelCT`), each
point of the code described in both runs by the same predicate `Φ a` of
public data `a` (`Two`, `Proof/Bignum/X86_64/Mont.lean`), with what
correctness says of each run added after each piece (`two_post`).

The code keeps its public values (pointers, lengths, MGF1's counter) in its
frame's slots, so the taint analysis starts from `rsp`, the base of the
frame (the first writable region), and the slots the piece reads, public
(`frT`), in two runs whose frames and regions agree (`FrV`, `two_taintF`).
The calls of the streaming hash functions are constant time when their
arguments agree (`two_init`, `two_upd`, `two_updExt`, `two_fin`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK UpdArgs FinArgs init_rel upd_rel fin_rel)

/-! ## The taint from the frame -/

/-- The registers `rs` and `rsp` public, `rsp` the base of the frame (the
first of `n + 1` writable regions), and the frame's words `ks` public. -/
def frT (rs : List Reg) (ks : List Nat) (n : Nat) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rsp]), flags := false, lens := frameBytes :: List.replicate n 0,
    bases := [(.rsp, 0, 0)],
    slots := ks.map fun k => (0, 8 * k, 8) }

/-- In the frame at `F`, with the writable regions `F`'s and the `n` of `ws`,
apart. -/
structure FrV (n : Nat) (F : Addr) (ws : List Region) (t : State) : Prop where
  rsp : t.gpr .rsp = F
  wr : t.wr = ⟨F, frameBytes⟩ :: ws
  two : ws.length = n
  pw : (⟨F, frameBytes⟩ :: ws : List Region).Pairwise Region.Disjoint
  len : ∀ r ∈ ws, r.len ≤ 2 ^ 64

theorem FrV.congr {n : Nat} {F : Addr} {ws : List Region} {t t' : State} (h : FrV n F ws t) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hwr : t'.wr = t.wr) : FrV n F ws t' :=
  ⟨hsp.trans h.rsp, hwr.trans h.wr, h.two, h.pw, h.len⟩

/-- Bytes of a word that both memories hold. -/
theorem word_byte {m₁ m₂ : Mem} {a : Addr} (h : m₁.readW a 64 = m₂.readW a 64) {j : Nat} (hj : j < 8) :
    m₁ (a + BitVec.ofNat 64 j) = m₂ (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m₁ a hj, ← Mem.extractLsb'_read m₂ a hj]
  simp only [Mem.readW, BitVec.setWidth_eq] at h
  rw [h]

theorem replicate_le (ws : List Region) :
    List.Forall₂ (fun r l => l ≤ r.len) ws (List.replicate ws.length 0) := by
  induction ws with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (Nat.zero_le _) ih

theorem frT_agree {n : Nat} {F : Addr} {ws : List Region} {rs : List Reg} {ks : List Nat} {t₁ t₂ : State}
    (h₁ : FrV n F ws t₁) (h₂ : FrV n F ws t₂) (hr : ∀ r ∈ rs, t₁.gpr r = t₂.gpr r) (hk : ∀ k ∈ ks, k < nW)
    (hw : ∀ k ∈ ks, word t₁.mem F (8 * k) = word t₂.mem F (8 * k)) : X86_64.Taint.Agree (frT rs ks n) t₁ t₂ := by
  have wf : ∀ {t : State}, FrV n F ws t → X86_64.Taint.Wf (frT rs ks n) t := fun h => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [h.wr, ← h.two]
      exact .cons (Nat.le_refl _) (replicate_le ws)
    · rw [h.wr]; exact h.pw
    · rw [h.wr]; intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · show frameBytes ≤ 2 ^ 64; decide
      · exact h.len r hr
    · simp only [frT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, h.wr, List.getD_cons_zero]
      rw [h.rsp, BitVec.add_zero]
  refine ⟨⟨fun r hr' => ?_, fun hf => by cases hf⟩, fun _ => by rw [h₁.wr, h₂.wr], wf h₁, wf h₂,
    fun sl hsl => ?_, fun sl hsl j hj₁ hj₂ => ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr') with hr' | hr'
    · exact hr r hr'
    · rw [List.mem_singleton.mp hr', h₁.rsp, h₂.rsp]
  · simp only [frT, List.mem_map] at hsl
    obtain ⟨k, hk', rfl⟩ := hsl
    have := hk k hk'
    simp only [frT, List.getD_cons_zero]
    unfold nW frameBytes at *; omega_using [this]
  · simp only [frT, List.mem_map] at hsl
    obtain ⟨k, hk', rfl⟩ := hsl
    simp only at hj₁ hj₂
    have hb : ∀ {t : State}, FrV n F ws t → X86_64.Taint.byteAddr t 0 j = off F (8 * k) + BitVec.ofNat 64 (j - 8 * k) :=
      fun h => by
        simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, h.wr, List.getD_cons_zero, off, BitVec.add_assoc,
          ← BitVec.ofNat_add]
        congr 2; omega_using [hj₁]
    rw [hb h₁, hb h₂]
    exact word_byte (hw k hk') (by omega_using [hj₂])

variable {α : Type}

/-- Code the taint analysis checks from `frT rs ks`, in two runs that `Φ a`
puts in the same frame, with the same words `ks` and registers `rs`. -/
theorem two_taintF {n : Nat} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (ks : List Nat)
    (F : α → Addr) (ws : α → List Region) (w : α → Nat → BitVec 64)
    (hv : ∀ a t, Φ a t → FrV n (F a) (ws a) t ∧ ∀ k ∈ ks, word t.mem (F a) (8 * k) = w a k)
    (hpin : Pins Φ rs) (hk : ∀ k ∈ ks, k < nW)
    (h : ∃ hc, (taint.check (frT rs ks n) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True := by
  obtain ⟨_, h⟩ := h
  refine RelCT.taint (A := taint) (frT rs ks n) (fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_) h
  obtain ⟨v₁, w₁⟩ := hv a t₁ h₁
  obtain ⟨v₂, w₂⟩ := hv a t₂ h₂
  exact frT_agree v₁ v₂ (hpin a _ _ h₁ h₂) hk fun k hk' => (w₁ k hk').trans (w₂ k hk').symm

/-- A piece checked by the taint analysis from `frT rs ks`, with what
correctness gives after it. -/
theorem two_pieceF {n : Nat} {Φ Ψ : α → State → Prop} {c : Prog isa} (rs : List Reg) (ks : List Nat)
    (F : α → Addr) (ws : α → List Region) (w : α → Nat → BitVec 64)
    (hv : ∀ a t, Φ a t → FrV n (F a) (ws a) t ∧ ∀ k ∈ ks, word t.mem (F a) (8 * k) = w a k)
    (hpin : Pins Φ rs) (hk : ∀ k ∈ ks, k < nW)
    (h : ∃ hc, (taint.check (frT rs ks n) c hc).isSome = true) (hw : ∀ a t, Φ a t → WP isa c t (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) :=
  two_post (two_taintF rs ks F ws w hv hpin hk h) hw

/-! ## The calls -/

variable {G : Stream} (hG : StreamOK G)

include hG in
/-- `init`, on the state at `scratch + oSt` in both runs. -/
theorem two_init {Φ : α → State → Prop} (F S : α → Addr)
    (h : ∀ a t, Φ a t → Lay t (F a) (S a) ∧ t.gpr .rdi = off (S a) oSt) :
    RelCT isa (Two Φ) (.call G.initN G.initC) fun _ _ => True := by
  have h1 : oSt + G.S ≤ oRsa := by have := (sizes hG).1; unfold oSt oRsa; omega_using [this]
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Φ a t₁ ∧ Φ a t₂) fun a =>
    init_rel hG (st := off (S a) oSt) fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  obtain ⟨L₁, d₁⟩ := h a t₁ p₁
  obtain ⟨L₂, d₂⟩ := h a t₂ p₂
  exact ⟨d₁, d₂, L₁.cov h1, L₂.cov h1, L₁.stk h1, L₂.stk h1, by rw [L₁.rsp, L₂.rsp]⟩

include hG in
/-- The arguments of `update` of the state with the `len` bytes at
`scratch + a`. -/
theorem updArgs {t : State} {F S : Addr} (L : Lay t F S) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + G.S ≤ a) (hwa : a + len ≤ oW ∨ oW + hG.Wb ≤ a)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S a) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oW) : UpdArgs hG t (off S oSt) (off S a) (off S oW) len := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega_using [hz]
  have h2 : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega_using [hz]
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega_using [hz]
  exact { rdi := hdi, rdx := hdx
          rcx := by rw [hcx, BitVec.toNat_ofNat]; unfold oRsa at ha; omega_using [ha]
          r8 := h8
          cd := Covers.right (L.cov ha)
          cw := Covers.pair (L.cov h1) (L.cov h2)
          st_sc := sdis S (Or.inl hsw) h1 h2
          d_st := sdis S hda ha h1
          d_sc := sdis S hwa ha h2
          stk_st := L.stk h1, stk_d := L.stk ha, stk_sc := L.stk h2 }

include hG in
/-- `update` with the `len a` bytes at `scratch + o a`, after `cnt a`. -/
theorem two_upd {Φ : α → State → Prop} (F S : α → Addr) (o len : α → Nat) (cnt : α → BitVec 64)
    (h : ∀ a t, Φ a t → Lay t (F a) (S a) ∧ o a + len a ≤ oRsa ∧ (o a + len a ≤ oSt ∨ oSt + G.S ≤ o a) ∧
      (o a + len a ≤ oW ∨ oW + hG.Wb ≤ o a) ∧ t.gpr .rdi = off (S a) oSt ∧ t.gpr .rsi = cnt a ∧
      t.gpr .rdx = off (S a) (o a) ∧ t.gpr .rcx = BitVec.ofNat 64 (len a) ∧ t.gpr .r8 = off (S a) oW) :
    RelCT isa (Two Φ) (.call G.updN G.updC) fun _ _ => True := by
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Φ a t₁ ∧ Φ a t₂) fun a =>
    upd_rel hG (st := off (S a) oSt) (d := off (S a) (o a)) (sc := off (S a) oW) (len := len a)
      fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  obtain ⟨L₁, a₁, b₁, c₁, d₁, e₁, f₁, g₁, i₁⟩ := h a t₁ p₁
  obtain ⟨L₂, -, -, -, d₂, e₂, f₂, g₂, i₂⟩ := h a t₂ p₂
  exact ⟨updArgs hG L₁ a₁ b₁ c₁ d₁ f₁ g₁ i₁, updArgs hG L₂ a₁ b₁ c₁ d₂ f₂ g₂ i₂, e₁.trans e₂.symm,
    by rw [L₁.rsp, L₂.rsp]⟩

include hG in
/-- `update` with the `len a` bytes at `d a`, outside our working space,
after `cnt a`. -/
theorem two_updExt {Φ : α → State → Prop} (F S d : α → Addr) (len : α → Nat) (cnt : α → BitVec 64)
    (h : ∀ a t, Φ a t → Lay t (F a) (S a) ∧ len a < 2 ^ 64 ∧ Covers [⟨d a, len a⟩] (t.rd ++ t.wr) ∧
      Region.Disjoint ⟨d a, len a⟩ ⟨S a, oRsa⟩ ∧ (below (F a) 16).Disjoint ⟨d a, len a⟩ ∧
      t.gpr .rdi = off (S a) oSt ∧ t.gpr .rsi = cnt a ∧ t.gpr .rdx = d a ∧
      t.gpr .rcx = BitVec.ofNat 64 (len a) ∧ t.gpr .r8 = off (S a) oW) :
    RelCT isa (Two Φ) (.call G.updN G.updC) fun _ _ => True := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega_using [hz]
  have h2 : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega_using [hz]
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega_using [hz]
  have args : ∀ a t, Φ a t → UpdArgs hG t (off (S a) oSt) (d a) (off (S a) oW) (len a) := fun a t p => by
    obtain ⟨L, hl, hcd, hds, hdk, hdi, -, hdx, hcx, h8⟩ := h a t p
    exact { rdi := hdi, rdx := hdx
            rcx := by rw [hcx, BitVec.toNat_ofNat]; omega_using [hl]
            r8 := h8
            cd := hcd
            cw := Covers.pair (L.cov h1) (L.cov h2)
            st_sc := sdis (S a) (Or.inl hsw) h1 h2
            d_st := hds.sub_right (Offset.sub_base (S a) h1)
            d_sc := hds.sub_right (Offset.sub_base (S a) h2)
            stk_st := L.stk h1, stk_d := by rw [L.rsp]; exact hdk, stk_sc := L.stk h2 }
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Φ a t₁ ∧ Φ a t₂) fun a =>
    upd_rel hG (st := off (S a) oSt) (d := d a) (sc := off (S a) oW) (len := len a)
      fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  obtain ⟨L₁, -, -, -, -, -, e₁, -⟩ := h a t₁ p₁
  obtain ⟨L₂, -, -, -, -, -, e₂, -⟩ := h a t₂ p₂
  exact ⟨args a t₁ p₁, args a t₂ p₂, e₁.trans e₂.symm, by rw [L₁.rsp, L₂.rsp]⟩

include hG in
/-- `finalize` to `scratch + o a`, after `cnt a`. -/
theorem two_fin {Φ : α → State → Prop} (F S : α → Addr) (o : α → Nat) (cnt : α → BitVec 64)
    (h : ∀ a t, Φ a t → Lay t (F a) (S a) ∧ (o a + 64 ≤ oSt ∨ (oSt + 256 ≤ o a ∧ o a + 64 ≤ oW)) ∧
      t.gpr .rdi = off (S a) oSt ∧ t.gpr .rsi = cnt a ∧ t.gpr .rdx = off (S a) (o a) ∧
      t.gpr .rcx = off (S a) oW) :
    RelCT isa (Two Φ) (.call G.finN G.finC) fun _ _ => True := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega_using [hz]
  have h2 : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega_using [hz]
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega_using [hz]
  have args : ∀ a t, Φ a t → FinArgs hG t (off (S a) oSt) (off (S a) (o a)) (off (S a) oW) := fun a t p => by
    obtain ⟨L, ho, hdi, -, hdx, hcx⟩ := h a t p
    have h3 : o a + G.F ≤ oRsa := by unfold oSt oW oRsa at *; omega_using [hz, ho]
    exact { rdi := hdi, rdx := hdx, rcx := hcx
            cw := Covers.cons (L.cov h1) (Covers.pair (L.cov h3) (L.cov h2))
            st_o := sdis (S a) (by unfold oSt oW at *; omega_using [hz, ho]) h1 h3
            st_sc := sdis (S a) (Or.inl hsw) h1 h2
            o_sc := sdis (S a) (by unfold oSt oW at *; omega_using [hz, ho]) h3 h2
            stk_st := L.stk h1, stk_o := L.stk h3, stk_sc := L.stk h2 }
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Φ a t₁ ∧ Φ a t₂) fun a =>
    fin_rel hG (st := off (S a) oSt) (o := off (S a) (o a)) (sc := off (S a) oW)
      fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  obtain ⟨L₁, -, -, e₁, -⟩ := h a t₁ p₁
  obtain ⟨L₂, -, -, e₂, -⟩ := h a t₂ p₂
  exact ⟨args a t₁ p₁, args a t₂ p₂, e₁.trans e₂.symm, by rw [L₁.rsp, L₂.rsp]⟩

end VG.Proof.RsaOaep.X86_64

end

end

/-!
# RSAES-OAEP on x86-64: MGF1 in constant time

Two runs of `mgfXor lay G` with the same frame, regions, `src` and `dst`
(`MQ`): the frame's public slots in a round (`RW`, `RW.words`), where MGF1
starts (`ME`), and the number of rounds (`nR`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs round xorOut nextCtr initArgs updSrcArgs updCtrArgs finArgs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post two_map two_loop)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

/-- MGF1's public data: the frame, the working space, the other two writable
regions, and `src` and `dst` in the working space. -/
structure MQ where
  F : Addr
  S : Addr
  ws : List Region
  src : Nat
  srcLen : Nat
  dst : Nat
  dstLen : Nat

/-- The frame's words MGF1 reads, with the counter `c`. -/
def mw (D : Nat) (q : MQ) (c k : Nat) : BitVec 64 :=
  if k = 14 then q.S else if k = 15 then off q.S q.src else if k = 16 then BitVec.ofNat 64 q.srcLen
  else if k = 17 then off q.S q.dst else if k = 18 then BitVec.ofNat 64 q.dstLen
  else if k = 19 then BitVec.ofNat 64 c else BitVec.ofNat 64 (c * D)

/-- A point of the round with counter `c`. -/
structure RW (n D : Nat) (q : MQ) (c : Nat) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  fit : MFit q.src q.srcLen q.dst q.dstLen
  lt : c * D < q.dstLen
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ MArgs W q.S q.src q.srcLen q.dst q.dstLen ∧
    W 19 = BitVec.ofNat 64 c ∧ W 20 = BitVec.ofNat 64 (c * D)

theorem RW.words {n D : Nat} {q : MQ} {c : Nat} {t : State} (h : RW n D q c t) :
    FrV n q.F q.ws t ∧ ∀ k ∈ [14, 15, 16, 17, 18, 19, 20], word t.mem q.F (8 * k) = mw D q c k := by
  obtain ⟨V, W, R, A, h19, h20⟩ := h.rep
  refine ⟨h.fv, fun k hk => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (slot_eq sScr 14 rfl _ _).symm.trans h.L.slot
  · rw [R.fr 15 (by decide), A.hsrc]; rfl
  · rw [R.fr 16 (by decide), A.hsl]; rfl
  · rw [R.fr 17 (by decide), A.hdst]; rfl
  · rw [R.fr 18 (by decide), A.hdl]; rfl
  · rw [R.fr 19 (by decide), h19]; rfl
  · rw [R.fr 20 (by decide), h20]; rfl

theorem RW.congr {n D : Nat} {q : MQ} {c : Nat} {t t' : State} (h : RW n D q c t) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) : RW n D q c t' :=
  ⟨h.fv.congr hsp hwr, h.L.congr hsp hwr (by rw [hm]), h.fit, h.lt, by rw [hm]; exact h.rep⟩

/-- After a piece that keeps the regions, with the slots as they were. -/
theorem RW.after {n D : Nat} {q : MQ} {c : Nat} {t t' : State} (h : RW n D q c t) (L' : Lay t' q.F q.S)
    (hwr : t'.wr = t.wr) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t'.mem q.F q.S V W)
    (A : MArgs W q.S q.src q.srcLen q.dst q.dstLen) (h19 : W 19 = BitVec.ofNat 64 c)
    (h20 : W 20 = BitVec.ofNat 64 (c * D)) : RW n D q c t' :=
  ⟨h.fv.congr (L'.rsp.trans h.L.rsp.symm) hwr, L', h.fit, h.lt, V, W, R, A, h19, h20⟩

variable {G : Stream} (hG : StreamOK G) (n : Nat)

/-! ## The points of a round -/

/-- A hash function's streaming functions of `hLen = d`, for the code that
depends on `hLen` alone. -/
def gD (d : Nat) : Stream := ⟨0, 0, d, 0, 0, "", .block [], "", .block [], "", .block []⟩

theorem nopin {β : Type} {Φ : β → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => absurd h List.not_mem_nil

/-! ## MGF1 -/

/-- Where MGF1 starts: in the frame, with its slots set. -/
structure ME (q : MQ) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  fit : MFit q.src q.srcLen q.dst q.dstLen
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ MArgs W q.S q.src q.srcLen q.dst q.dstLen

/-- The number of rounds. -/
def nR (D : Nat) (q : MQ) : Nat := (q.dstLen + D - 1) / D

theorem lt_nR {D : Nat} (hD : 0 < D) (q : MQ) (j : Nat) : j < nR D q ↔ j * D < q.dstLen := by
  unfold nR
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le hD, Nat.succ_mul]
  omega_using [hD]

end VG.Proof.RsaOaep.X86_64

end

end

/-!
# RSAES-OAEP on x86-64: the label's hash in constant time

`hashLabel G o` is constant time in two runs with the same frame, regions
and label's address and length (`LQ`), whatever the label (`hashLabel_ct`):
the blocks between the calls are checked by the taint analysis, and the
calls' arguments are the same in both runs.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

/-- The label's hash's public data: the frame, the working space, the other
two writable regions, and the label's address and length. -/
structure LQ where
  F : Addr
  S : Addr
  ws : List Region
  lab : Addr
  labLen : Nat

/-- A point of `hashLabel`. -/
structure LW (n : Nat) (q : LQ) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ LabAt t q.F q.S W q.lab q.labLen

theorem LW.congr {n : Nat} {q : LQ} {t t' : State} (h : LW n q t) (hsp : t'.gpr .rsp = t.gpr .rsp) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) : LW n q t' := by
  obtain ⟨V, W, R, A⟩ := h.rep
  exact ⟨h.fv.congr hsp hwr, h.L.congr hsp hwr (by rw [hm]), V, W, hm ▸ R, A.congr hrd hwr rfl rfl⟩

theorem LW.after {n : Nat} {q : LQ} {t t' : State} (h : LW n q t) (L' : Lay t' q.F q.S) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t'.mem q.F q.S V W)
    (A : LabAt t q.F q.S W q.lab q.labLen) : LW n q t' :=
  ⟨h.fv.congr (L'.rsp.trans h.L.rsp.symm) hwr, L', V, W, R, A.congr hrd hwr rfl rfl⟩

theorem LW.fr {n : Nat} {q : LQ} {t : State} (h : LW n q t) : FrV n q.F q.ws t ∧ ∀ k ∈ ([] : List Nat), word t.mem q.F (8 * k) = 0 :=
  ⟨h.fv, fun _ h => absurd h List.not_mem_nil⟩

variable {G : Stream} (hG : StreamOK G)

include hG in
/-- The label's hash to `scratch + o`, in two runs with the same `LQ`. -/
theorem hashLabel_ct (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) {o : Nat} (ho : o = oDig ∨ o = oLh) :
    RelCT isa (Two (LW n)) (hashLabel G o) fun _ _ => True := by
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  unfold hashLabel seqs seqs seqs seqs seqs
  refine RelCT.seq (two_pieceF (Ψ := fun q t => LW n q t ∧ t.gpr .rdi = off q.S oSt) [] [] LQ.F LQ.ws (fun _ _ => 0)
    (fun q t h => h.fr) nopin (by decide) (by rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h =>
      WP.mono (scr_ok h.L (d := .rdi) (by decide) (o := oSt) (by decide))
        fun t' ⟨hdi, hm, k⟩ => ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm, hdi⟩) ?_
  refine RelCT.seq (two_post (Ψ := LW n) (two_init hG LQ.F LQ.S fun q t h => ⟨h.1.L, h.2⟩) fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.1.rep
    exact WP.mono (init_ok hG h.1.L R h.2) fun t' ⟨L', rd', wr', _, R', _⟩ => h.1.after L' rd' wr' R' A
  refine RelCT.seq (two_pieceF (Ψ := fun q t => LW n q t ∧ t.gpr .rdi = off q.S oSt ∧
      t.gpr .rsi = BitVec.ofNat 64 0 ∧ t.gpr .rdx = q.lab ∧ t.gpr .rcx = BitVec.ofNat 64 q.labLen ∧
      t.gpr .r8 = off q.S oW) [] [] LQ.F LQ.ws (fun _ _ => 0)
    (fun q t h => h.fr) nopin (by decide) (by rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.rep
    exact WP.mono (labA_ok h.L R A) fun t' ⟨hdi, hsi, hdx, hcx, h8, hm, k⟩ =>
      ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := LW n) (two_updExt hG LQ.F LQ.S LQ.lab LQ.labLen (fun _ => BitVec.ofNat 64 0)
    fun q t h => by
      obtain ⟨V, W, R, A⟩ := h.1.rep
      exact ⟨h.1.L, A.len, A.cov, A.dS, A.dK, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.1.rep
    exact WP.mono (updExt_ok hG h.1.L R A.len A.cov A.dS A.dK h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
      fun t' ⟨L', rd', wr', _, R', _⟩ => h.1.after L' rd' wr' R' A
  refine RelCT.seq (two_pieceF (Ψ := fun q t => LW n q t ∧ t.gpr .rdi = off q.S oSt ∧
      t.gpr .rsi = BitVec.ofNat 64 q.labLen ∧ t.gpr .rdx = off q.S o ∧ t.gpr .rcx = off q.S oW) [] [] LQ.F LQ.ws
    (fun _ _ => 0) (fun q t h => h.fr) nopin (by decide) (by rcases ho with rfl | rfl <;> rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.rep
    exact WP.mono (labF_ok h.L R A.hll (o := o) (by rcases ho with rfl | rfl <;> decide))
      fun t' ⟨hdi, hsi, hdx, hcx, hm, k⟩ => ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm, hdi, hsi, hdx, hcx⟩
  exact two_fin hG LQ.F LQ.S (fun _ => o) (fun q => BitVec.ofNat 64 q.labLen)
    fun q t h => ⟨h.1.L, Or.inr hoo, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end VG.Proof.RsaOaep.X86_64
