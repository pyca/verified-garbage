import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-!
# RSASSA-PSS on x86-64: two runs, and their public frame

The constant-time proofs relate two runs piece by piece (`RelCT`). The
pieces between the calls are checked by the taint analysis from `pT n ks rs`:
the registers `rs` and `rsp` public, `rsp` the base of the frame (the first
writable region, followed by `n` more) and the words `ks` of the frame
public. At the start of a piece both runs are described by the same public
values (`Pub`): the frame, the working space, the writable regions, the
public words of the frame and the public registers; `Pub` in both runs gives
the agreement the taint analysis starts from (`pub_agree`).

The secret stores of a piece (through pointers into the working space the
analysis does not follow) make it forget the public words, so each piece
starts from what the correctness proof says of both runs.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Bignum.X86_64 (off Two)

/-- The taint at the start of a piece. -/
def pT (n : Nat) (ks : List Nat) (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rsp]), flags := false, lens := frameBytes :: List.replicate n 0,
    bases := [(.rsp, 0, 0)], slots := ks.map fun k => (0, 8 * k, 8) }

/-- What a run shows at the start of a piece: its frame `F` (at `rsp`), its
working space `S`, the writable regions after the frame, the public words of
the frame (`ws`, by index) and the public registers (`rs`), and what else is
true of it (`X`, of its working space and frame). -/
structure Pub (F S : Addr) (rest : List Region) (ws : List (Nat × BitVec 64)) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) (t : State) : Prop where
  L : Lay t F S
  wr : t.wr = ⟨F, frameBytes⟩ :: rest
  W : ∃ V W, Rep t.mem F S V W ∧ (∀ p ∈ ws, W p.1 = p.2) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2

/-- The writable regions after the frame, as the analysis needs them. -/
structure RestOk (n : Nat) (F : Addr) (rest : List Region) : Prop where
  len : rest.length = n
  dis : (⟨F, frameBytes⟩ :: rest).Pairwise Region.Disjoint
  fit : ∀ r ∈ rest, r.len ≤ 2 ^ 64

/-- The bytes of a word that two memories hold. -/
theorem word_byte {m₁ m₂ : Mem} {a : Addr} (h : m₁.readW a 64 = m₂.readW a 64) {j : Nat} (hj : j < 8) :
    m₁ (a + BitVec.ofNat 64 j) = m₂ (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m₁ a hj, ← Mem.extractLsb'_read m₂ a hj]
  have e : ∀ m : Mem, m.readW a 64 = m.read a 8 := fun m => by simp [Mem.readW]
  rw [← e, ← e, h]

theorem forall₂_lens {F : Addr} : ∀ {rest : List Region} {n : Nat}, rest.length = n →
    List.Forall₂ (fun r l => l ≤ r.len) (⟨F, frameBytes⟩ :: rest) (frameBytes :: List.replicate n 0)
  | [], 0, _ => .cons (Nat.le_refl _) .nil
  | r :: rest, n + 1, h => by
    have := forall₂_lens (F := F) (rest := rest) (n := n) (by simpa using h)
    cases this with
    | cons h₁ h₂ => exact .cons h₁ (.cons (Nat.zero_le _) h₂)

theorem wf_of {F : Addr} {rest : List Region} {t : State} {n : Nat} (hsp : t.gpr .rsp = F)
    (hw : t.wr = ⟨F, frameBytes⟩ :: rest) (hr : RestOk n F rest) (ks : List Nat) (rgs : List Reg) :
    X86_64.Taint.Wf (pT n ks rgs) t := by
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
  · rw [hw]; exact forall₂_lens hr.len
  · rw [hw]; exact hr.dis
  · rw [hw]; intro r hr'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · show frameBytes ≤ 2 ^ 64; decide
    · exact hr.fit r hr'
  · simp only [pT, List.mem_singleton] at hp; subst hp
    simp only [X86_64.Taint.region, hw, List.getD_cons_zero]
    rw [hsp, BitVec.add_zero]

theorem pub_wf {F S : Addr} {rest : List Region} {ws : List (Nat × BitVec 64)} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} {t : State} {n : Nat} (h : Pub F S rest ws rs X t)
    (hr : RestOk n F rest) (ks : List Nat) (rgs : List Reg) :
    X86_64.Taint.Wf (pT n ks rgs) t :=
  wf_of h.L.rsp h.wr hr ks rgs

/-- Before the frame is set up: the analysis starts from `pT n []`. -/
theorem two_pub0 {α : Type} {Φ : α → State → Prop} {c : Prog isa} (n : Nat) (rgs : List Reg)
    (F : α → Addr) (rest : α → List Region) (rs : α → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → t.gpr .rsp = F a ∧ t.wr = ⟨F a, frameBytes⟩ :: rest a ∧ ∀ p ∈ rs a, t.gpr p.1 = p.2)
    (hR : ∀ a t, Φ a t → RestOk n (F a) (rest a)) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT n [] rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True := by
  refine RelCT.taint (A := taint) (pT n [] rgs) (fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_) h
  obtain ⟨sp₁, w₁, r₁⟩ := hΦ a _ h₁
  obtain ⟨sp₂, w₂, r₂⟩ := hΦ a _ h₂
  refine ⟨⟨fun r hr' => ?_, fun hf => by cases hf⟩, fun _ => by rw [w₁, w₂], wf_of sp₁ w₁ (hR a _ h₁) _ _,
    wf_of sp₂ w₂ (hR a _ h₁) _ _, fun sl hsl => by simp [pT] at hsl, fun sl hsl => by simp [pT] at hsl,
    X86_64.Taint.noLo⟩
  rcases List.mem_append.mp (RegSet.mem_ofList.mp hr') with hr' | hr'
  · rw [← hr a] at hr'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr'
    rw [r₁ p hp, r₂ p hp]
  · rw [List.mem_singleton.mp hr', sp₁, sp₂]

/-- Both runs show the same public values: the analysis starts from `pT`. -/
theorem pub_agree {F S : Addr} {rest : List Region} {ws : List (Nat × BitVec 64)} {rs : List (Reg × BitVec 64)}
    {X₁ X₂ : (Nat → Byte) → (Nat → BitVec 64) → Prop} {t₁ t₂ : State} {n : Nat}
    (h₁ : Pub F S rest ws rs X₁ t₁) (h₂ : Pub F S rest ws rs X₂ t₂) (hr : RestOk n F rest)
    (hks : ∀ p ∈ ws, p.1 < nW) : X86_64.Taint.Agree (pT n (ws.map Prod.fst) (rs.map Prod.fst)) t₁ t₂ := by
  refine ⟨⟨fun r hr' => ?_, fun hf => by cases hf⟩, fun _ => by rw [h₁.wr, h₂.wr], pub_wf h₁ hr _ _,
    pub_wf h₂ hr _ _, fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr') with hr' | hr'
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr'
      rw [h₁.regs p hp, h₂.regs p hp]
    · rw [List.mem_singleton.mp hr', h₁.L.rsp, h₂.L.rsp]
  · simp only [pT, List.mem_map, List.map_map] at hsl
    obtain ⟨p, hp, rfl⟩ := hsl
    have := hks p hp
    simp only [pT, List.getD_cons_zero, Function.comp]
    unfold nW frameBytes at *; omega
  · simp only [pT, List.mem_map, List.map_map] at hsl
    obtain ⟨p, hp, rfl⟩ := hsl
    have hk := hks p hp
    simp only [Function.comp_apply] at hk₁ hk₂ ⊢
    have hb : ∀ t : State, t.wr = ⟨F, frameBytes⟩ :: rest → X86_64.Taint.byteAddr t 0 k =
        off F (8 * p.1) + BitVec.ofNat 64 (k - 8 * p.1) := fun t hw => by
      simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_zero, off, BitVec.add_assoc,
        BitVec.ofNat_add_ofNat]
      congr 2; omega
    rw [hb t₁ h₁.wr, hb t₂ h₂.wr]
    obtain ⟨V₁, W₁, R₁, hw₁, -⟩ := h₁.W
    obtain ⟨V₂, W₂, R₂, hw₂, -⟩ := h₂.W
    refine word_byte ?_ (by omega)
    have e₁ := R₁.fr p.1 hk
    have e₂ := R₂.fr p.1 hk
    simp only [Bignum.X86_64.word] at e₁ e₂
    rw [e₁, e₂, hw₁ p hp, hw₂ p hp]

/-- A piece the analysis checks from `pT`, between states that show the same
public values. -/
theorem two_pub {α : Type} {Φ : α → State → Prop} {c : Prog isa} (n : Nat) (ks : List Nat) (rgs : List Reg)
    (F S : α → Addr) (rest : α → List Region) (ws : α → List (Nat × BitVec 64)) (rs : α → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ X, Pub (F a) (S a) (rest a) (ws a) (rs a) X t)
    (hR : ∀ a t, Φ a t → RestOk n (F a) (rest a)) (hk : ∀ a, (ws a).map Prod.fst = ks) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT n ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (pT n ks rgs) (fun _ _ ⟨a, h₁, h₂⟩ => by
    obtain ⟨X₁, p₁⟩ := hΦ a _ h₁
    obtain ⟨X₂, p₂⟩ := hΦ a _ h₂
    have := pub_agree p₁ p₂ (hR a _ h₁) (fun p hp => hks p.1 (by rw [← hk a]; exact List.mem_map_of_mem hp))
    rwa [hk a, hr a] at this) h

end VG.Proof.RsaPss.X86_64
