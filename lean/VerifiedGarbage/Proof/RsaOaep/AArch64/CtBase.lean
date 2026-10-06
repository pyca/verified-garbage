import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# RSAES-OAEP on AArch64: relating two runs of the pieces

The pieces that encryption and decryption share (MGF1, the label's hash)
relate two runs in the same frame `F` with the same working space `S`
(`LR`): each has the pieces' `Lay` and `Rep`, and satisfies `X`, which fixes
the registers the next piece's addresses and arguments depend on as
functions of public data. Memory is secret to the taint analysis (a loaded
value is secret), so a block that dereferences a pointer it loads is split
there (`lr_seq_tr`), the registers its second part dereferences fixed by
its first part in both runs. A call of the streaming hash functions is the
same call in both runs (`lr_init`, `lr_upd`, `lr_updExt`, `lr_fin`).
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK UpdArgs FinArgs init_rel upd_rel fin_rel)

/-- Two runs in the frame `F` with the working space `S`, each with `X` of
its frame's words. -/
def LR (F S : Addr) (X : (Nat → BitVec 64) → State → Prop) (a b : State) : Prop :=
  (∃ V W, Lay a F S ∧ Rep a.mem F S V W ∧ X W a) ∧ (∃ V W, Lay b F S ∧ Rep b.mem F S V W ∧ X W b)

theorem LR.sp {F S : Addr} {X : (Nat → BitVec 64) → State → Prop} {a b : State} (h : LR F S X a b) :
    a.sp = b.sp := by
  obtain ⟨⟨_, _, La, _⟩, ⟨_, _, Lb, _⟩⟩ := h
  exact La.sp.trans Lb.sp.symm

/-- What a piece establishes, by correctness. -/
abbrev LRStep (F S : Addr) (c : Prog isa) (X X' : (Nat → BitVec 64) → State → Prop) : Prop :=
  ∀ (t : State) V W, Lay t F S → Rep t.mem F S V W → X W t →
    WP isa c t fun u => ∃ V' W', Lay u F S ∧ Rep u.mem F S V' W' ∧ X' W' u

theorem lr_wp {F S : Addr} {c : Prog isa} {X X' : (Nat → BitVec 64) → State → Prop}
    (hct : RelCT isa (LR F S X) c fun _ _ => True) (hw : LRStep F S c X X') :
    RelCT isa (LR F S X) c (LR F S X') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨V₁, W₁, L₁, R₁, x₁⟩, ⟨V₂, W₂, L₂, R₂, x₂⟩⟩ := hp
  obtain ⟨_, u₁, y₁, z₁⟩ := hw s₁ _ _ L₁ R₁ x₁
  obtain ⟨_, u₂, y₂, z₂⟩ := hw s₂ _ _ L₂ R₂ x₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ y₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ y₂
  exact ⟨ht, z₁, z₂⟩

/-- Code checked by the taint analysis from the registers `rs`, which `X` fixes. -/
theorem lr_taint {F S : Addr} {c : Prog isa} {X : (Nat → BitVec 64) → State → Prop} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ W₁ W₂ a b, X W₁ a → X W₂ b → ∀ r ∈ rs, a.gpr r = b.gpr r) :
    RelCT isa (LR F S X) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ hp => by
    have hs := hp.sp
    obtain ⟨⟨_, _, _, _, x₁⟩, ⟨_, _, _, _, x₂⟩⟩ := hp
    exact ⟨hs, fun r hr => hag _ _ _ _ x₁ x₂ r (Taint.mem_ofRegs.mp hr)⟩) h

/-- No registers to fix. -/
theorem nopin {X : (Nat → BitVec 64) → State → Prop} :
    ∀ W₁ W₂ (a b : State), X W₁ a → X W₂ b → ∀ r ∈ ([] : List Reg), a.gpr r = b.gpr r :=
  fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil

/-- Code whose second part `c₂` dereferences the registers `rs`, which its
first part `c₁` sets to `pin` in both runs. -/
theorem lr_seq_tr {F S : Addr} {c₁ c₂ : Prog isa} {X : (Nat → BitVec 64) → State → Prop}
    (rs : List Reg) (pin : Reg → BitVec 64) {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs []) c₁ h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs rs) c₂ h₂).isSome = true)
    (hA : ∀ (t : State) V W, Lay t F S → Rep t.mem F S V W → X W t →
      WP isa c₁ t fun u => u.sp = t.sp ∧ ∀ r ∈ rs, u.gpr r = pin r) :
    RelCT isa (LR F S X) (.seq c₁ c₂) fun _ _ => True := by
  have h1 : RelCT isa (LR F S X) c₁ fun a b => a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r := by
    have hw := (RelCT.taint (A := taint) (P := LR F S X) (Taint.ofRegs []) (fun _ _ hp =>
      ⟨hp.sp, fun r hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩) t₁).wpDep
      (F := fun (s u : State) => u.sp = s.sp ∧ ∀ r ∈ rs, u.gpr r = pin r) fun s₁ s₂ hp => by
        obtain ⟨⟨V₁, W₁, L₁, R₁, x₁⟩, ⟨V₂, W₂, L₂, R₂, x₂⟩⟩ := hp
        exact ⟨hA _ _ _ L₁ R₁ x₁, hA _ _ _ L₂ R₂ x₂⟩
    refine hw.mono (fun _ _ h => h) fun a b ⟨_, σ₁, σ₂, hσ, ⟨sa, ra⟩, ⟨sb, rb⟩⟩ =>
      ⟨by rw [sa, sb]; exact hσ.sp, fun r hr => (ra r hr).trans (rb r hr).symm⟩
  have h2 : RelCT isa (fun a b => a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r) c₂ fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ ⟨hs, hr⟩ =>
      ⟨hs, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) t₂
  exact h1.seq h2

/-- `d ← scratch + o`, in both runs the same. -/
theorem scr_pin {t : State} {F S : Addr} (L : Lay t F S) (d : Reg) {o : Nat} (ho : o < 4096) :
    WP isa (.block (scr d o)) t fun u => u.sp = t.sp ∧ u.gpr d = off S o := by
  have h96 : InRegions (t.rd ++ t.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : t.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  oaep_run [scr, Mgf1.scr, lay, sScr, h96, L.sp, hs, ho]

/-- A loop counting down in `cr` from `n`, whose runs agree on `P k` after `k` iterations. -/
theorem count_ct {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (P : Nat → State → State → Prop)
    (hstep : ∀ k < n, RelCT isa (P k) body fun a b =>
      P (k + 1) a b ∧ (a.gpr cr != 0) = decide (k + 1 ≠ n) ∧ (b.gpr cr != 0) = decide (k + 1 ≠ n)) :
    RelCT isa (P 0) (.loop body (.nonzero .x cr)) (P n) := by
  refine (RelCT.loop (fun m a b => ∃ k, k < n ∧ m = n - k ∧ P k a b) (fun m => RelCT.exists_ fun k => ?_) n).mono
    (fun a b h => ⟨0, hn, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hk, hm, hp⟩ e₁ e₂
  obtain ⟨ht, hq, c₁, c₂⟩ := hstep k hk _ _ _ _ _ _ hp e₁ e₂
  refine ⟨ht, by rw [eval_nonzero, eval_nonzero, c₁, c₂], fun h => ?_, fun h => ?_⟩
  · rw [eval_nonzero, c₁] at h
    have : k + 1 = n := by simpa using h
    exact this ▸ hq
  · rw [eval_nonzero, c₁] at h
    have : k + 1 ≠ n := by simpa using h
    exact ⟨n - (k + 1), by omega, k + 1, by omega, rfl, hq⟩

/-! ## The calls -/

variable {G : Stream} (hG : StreamOK G)

include hG in
theorem lr_init {F S : Addr} {X : (Nat → BitVec 64) → State → Prop}
    (hx : ∀ W (t : State), X W t → t.gpr .x0 = off S oSt) :
    RelCT isa (LR F S X) (.call G.initN G.initC) fun _ _ => True := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  exact init_rel hG (st := off S oSt) fun a b h => by
    have hs := h.sp
    obtain ⟨⟨_, Wa, La, _, xa⟩, ⟨_, Wb, Lb, _, xb⟩⟩ := h
    exact ⟨hx _ _ xa, hx _ _ xb, La.cov h1, Lb.cov h1, hs⟩

include hG in
/-- `update` with the `len` bytes at `scratch + a`, after `x1` bytes. -/
theorem lr_upd {F S : Addr} {X : (Nat → BitVec 64) → State → Prop} {a len : Nat} (x1 : BitVec 64)
    (ha : a + len ≤ oRsa) (hda : a + len ≤ oSt ∨ oSt + G.S ≤ a) (hwa : a + len ≤ oW ∨ oW + hG.Wb ≤ a)
    (hx : ∀ W (t : State), X W t → t.gpr .x0 = off S oSt ∧ t.gpr .x1 = x1 ∧ t.gpr .x2 = off S a ∧
      t.gpr .x3 = BitVec.ofNat 64 len ∧ t.gpr .x4 = off S oW) :
    RelCT isa (LR F S X) (.call G.updN G.updC) fun _ _ => True :=
  upd_rel hG fun a b h => by
    have hs := h.sp
    obtain ⟨⟨_, Wa, La, _, xa⟩, ⟨_, Wb, Lb, _, xb⟩⟩ := h
    obtain ⟨a0, a1, a2, a3, a4⟩ := hx _ _ xa
    obtain ⟨b0, b1, b2, b3, b4⟩ := hx _ _ xb
    exact ⟨updArgs_of hG La ha hda hwa a0 a2 a3 a4, updArgs_of hG Lb ha hda hwa b0 b2 b3 b4, a1.trans b1.symm, hs⟩

include hG in
/-- `update` with the `len` bytes at `d`, outside our working space. -/
theorem lr_updExt {F S : Addr} {X : (Nat → BitVec 64) → State → Prop} {d : Addr} {len : Nat} (x1 : BitVec 64)
    (hlen : len < 2 ^ 64)
    (hx : ∀ W (t : State), X W t → (Covers [⟨d, len⟩] (t.rd ++ t.wr) ∧ Region.Disjoint ⟨d, len⟩ ⟨S, oRsa⟩ ∧
      (below F 16).Disjoint ⟨d, len⟩) ∧ t.gpr .x0 = off S oSt ∧ t.gpr .x1 = x1 ∧
      t.gpr .x2 = d ∧ t.gpr .x3 = BitVec.ofNat 64 len ∧ t.gpr .x4 = off S oW) :
    RelCT isa (LR F S X) (.call G.updN G.updC) fun _ _ => True :=
  upd_rel hG fun a b h => by
    have hs := h.sp
    obtain ⟨⟨_, Wa, La, _, xa⟩, ⟨_, Wb, Lb, _, xb⟩⟩ := h
    obtain ⟨⟨ac, ads, adk⟩, a0, a1, a2, a3, a4⟩ := hx _ _ xa
    obtain ⟨⟨bc, bds, bdk⟩, b0, b1, b2, b3, b4⟩ := hx _ _ xb
    exact ⟨updExtArgs_of hG La hlen ac ads adk a0 a2 a3 a4, updExtArgs_of hG Lb hlen bc bds bdk b0 b2 b3 b4,
      a1.trans b1.symm, hs⟩

include hG in
/-- `finalize` to `scratch + o`, after `x1` bytes. -/
theorem lr_fin {F S : Addr} {X : (Nat → BitVec 64) → State → Prop} {o : Nat} (x1 : BitVec 64)
    (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (hx : ∀ W (t : State), X W t → t.gpr .x0 = off S oSt ∧ t.gpr .x1 = x1 ∧ t.gpr .x2 = off S o ∧
      t.gpr .x3 = off S oW) :
    RelCT isa (LR F S X) (.call G.finN G.finC) fun _ _ => True :=
  fin_rel hG fun a b h => by
    have hs := h.sp
    obtain ⟨⟨_, Wa, La, _, xa⟩, ⟨_, Wb, Lb, _, xb⟩⟩ := h
    obtain ⟨a0, a1, a2, a3⟩ := hx _ _ xa
    obtain ⟨b0, b1, b2, b3⟩ := hx _ _ xb
    exact ⟨finArgs_of hG La ho a0 a2 a3, finArgs_of hG Lb ho b0 b2 b3, a1.trans b1.symm, hs⟩

end VG.Proof.RsaOaep.AArch64
