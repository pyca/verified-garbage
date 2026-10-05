import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Bignum.X86_64.Mont

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

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Bignum.X86_64 (off word Two Pins two_post)
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
    fun sl hsl => ?_, fun sl hsl j hj₁ hj₂ => ?_, X86_64.Taint.noLo⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr') with hr' | hr'
    · exact hr r hr'
    · rw [List.mem_singleton.mp hr', h₁.rsp, h₂.rsp]
  · simp only [frT, List.mem_map] at hsl
    obtain ⟨k, hk', rfl⟩ := hsl
    have := hk k hk'
    simp only [frT, List.getD_cons_zero]
    unfold nW frameBytes at *; omega
  · simp only [frT, List.mem_map] at hsl
    obtain ⟨k, hk', rfl⟩ := hsl
    simp only at hj₁ hj₂
    have hb : ∀ {t : State}, FrV n F ws t → X86_64.Taint.byteAddr t 0 j = off F (8 * k) + BitVec.ofNat 64 (j - 8 * k) :=
      fun h => by
        simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, h.wr, List.getD_cons_zero, off, BitVec.add_assoc,
          ← BitVec.ofNat_add]
        congr 2; omega
    rw [hb h₁, hb h₂]
    exact word_byte (hw k hk') (by omega)

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
  have h1 : oSt + G.S ≤ oRsa := by have := (sizes hG).1; unfold oSt oRsa; omega
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
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega
  exact { rdi := hdi, rdx := hdx
          rcx := by rw [hcx, BitVec.toNat_ofNat]; unfold oRsa at ha; omega
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
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega
  have args : ∀ a t, Φ a t → UpdArgs hG t (off (S a) oSt) (d a) (off (S a) oW) (len a) := fun a t p => by
    obtain ⟨L, hl, hcd, hds, hdk, hdi, -, hdx, hcx, h8⟩ := h a t p
    exact { rdi := hdi, rdx := hdx
            rcx := by rw [hcx, BitVec.toNat_ofNat]; omega
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
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega
  have args : ∀ a t, Φ a t → FinArgs hG t (off (S a) oSt) (off (S a) (o a)) (off (S a) oW) := fun a t p => by
    obtain ⟨L, ho, hdi, -, hdx, hcx⟩ := h a t p
    have h3 : o a + G.F ≤ oRsa := by unfold oSt oW oRsa at *; omega
    exact { rdi := hdi, rdx := hdx, rcx := hcx
            cw := Covers.cons (L.cov h1) (Covers.pair (L.cov h3) (L.cov h2))
            st_o := sdis (S a) (by unfold oSt oW at *; omega) h1 h3
            st_sc := sdis (S a) (Or.inl hsw) h1 h2
            o_sc := sdis (S a) (by unfold oSt oW at *; omega) h3 h2
            stk_st := L.stk h1, stk_o := L.stk h3, stk_sc := L.stk h2 }
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Φ a t₁ ∧ Φ a t₂) fun a =>
    fin_rel hG (st := off (S a) oSt) (o := off (S a) (o a)) (sc := off (S a) oW)
      fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  obtain ⟨L₁, -, -, e₁, -⟩ := h a t₁ p₁
  obtain ⟨L₂, -, -, e₂, -⟩ := h a t₂ p₂
  exact ⟨args a t₁ p₁, args a t₂ p₂, e₁.trans e₂.symm, by rw [L₁.rsp, L₂.rsp]⟩

end VG.Proof.RsaOaep.X86_64
