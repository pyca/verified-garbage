module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.R2
public import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.R2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_precompute` on x86-64: `R_X² mod X` is constant time

`double` and `doubles` leak the same in runs with the same workspace and
count, whatever their moduli and `-m⁻¹` (`double_ctW`, `doubles_ctW`), and
so do `r2X` (`r2X_ct`), whose loop and branches count the lengths, and
`r2At` (`r2At_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PrivPre (r2X r2At link bW chunkWords fixStart fixStep fixStepB fixSub)

/-- `DblHeadL`, which does not read `-m⁻¹`, for a workspace. -/
def DblHeadW (mo acc tmp o : Nat) (L : Ws) (t : State) : Prop := DblHeadL mo acc tmp o ⟨L.B, L.Z, L.w, 0⟩ t

/-- `double` leaks the same in runs with the same workspace. -/
theorem double_ctW {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true) :
    RelCT isa (Two GoodW) (double mo acc tmp o) fun _ _ => True :=
  RelCT.seq (two_piece (Ψ := DblHeadW mo acc tmp o) _ pins_goodW h fun L _ ⟨minv, hg⟩ =>
      dblHead_ok (L := ⟨L.B, L.Z, L.w, minv⟩) hg hmo hacc htmp ho)
    (two_taint _ (fun L => pins_dblHead mo acc tmp o ⟨L.B, L.Z, L.w, 0⟩) (by taint_decide))

/-- The public data of `doubles` in a workspace whose `-m⁻¹` is secret. -/
structure DblPubW where
  L : Ws
  c : Nat

/-- What `doubles` keeps, after `j` doublings. -/
def DblsAtW (mo acc tmp o sl : Nat) (p : DblPubW) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (O N : Nat) (minv : BitVec 64), DblsInv σ p.L.B p.L.Z p.L.w minv mo acc tmp o sl p.c O N j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ p.c < 2 ^ 31 ∧ 0 < N

theorem dblsAtW_good {mo acc tmp o sl : Nat} {p : DblPubW} {j : Nat} {t : State}
    (h : DblsAtW mo acc tmp o sl p j t) : GoodW p.L t :=
  let ⟨_, _, _, minv, hI, hZ, _⟩ := h; ⟨minv, ⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩

/-- `doubles` leaks the same in runs with the same workspace and count. -/
theorem doubles_ctW {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.rdi]) (.block [.store (hdr sl) .rcx]) hc').isSome = true)
    {hc'' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h'' : (taint.check (Taint.ofRegs [.rdi]) (.block (dblCount sl)) hc'').isSome = true) :
    RelCT isa (Two fun (p : DblPubW) s => ∃ minv, GoodL ⟨p.L.B, p.L.Z, p.L.w, minv⟩ s ∧ 2 ≤ p.L.w ∧
      p.L.w < 2 ^ 31 ∧ 1 ≤ p.c ∧ p.c < 2 ^ 31 ∧ s.gpr .rcx = BitVec.ofNat 64 p.c ∧
      wv s.mem p.L.B (slot p.L.w o) p.L.w < wv s.mem p.L.B (slot p.L.w mo) p.L.w)
      (doubles mo acc tmp o sl) fun _ _ => True := by
  rw [doubles_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ DblsAtW mo acc tmp o sl p 0 s) _
    (fun p s₁ s₂ ⟨m₁, h₁, _⟩ ⟨m₂, h₂, _⟩ => pins_goodW ⟨p.L.B, p.L.Z, p.L.w⟩ s₁ s₂ ⟨m₁, h₁⟩ ⟨m₂, h₂⟩) h' ?_) ?_
  · rintro p s ⟨minv, hg, hw, hw', hc1, hc', hcx, hO⟩
    exact WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hg.1.scr hg.1.rdi hg.1.hdr hg.2 hmo ho hsl hsl' hcx hO)
      fun t hI => ⟨by omega, s, _, _, minv, hI, hg.2, hw, hw', hc', Nat.lt_of_le_of_lt (Nat.zero_le _) hO⟩
  refine RelCT.mono (two_loop (Φ := DblsAtW mo acc tmp o sl) (Ψ := fun _ _ => True) (fun p => p.c) ?_ ?_)
    (fun _ _ h => h) fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : DblPubW × Nat) s => GoodW q.1.L s)
      (two_map (·.1.L) (fun _ _ h => dblsAtW_good h.2) (double_ctW hmo hacc htmp ho h)) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_goodW q.1.L s₁ s₂ h₁ h₂) h'')
    rintro ⟨p, j⟩ s ⟨hj, σ, O, N, minv, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (double_ok hI.scr hI.rdi hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t ⟨_, ha, k⟩ =>
        ⟨minv, ⟨hI.scr.congr k.2.2, (k.gpr (by decide)).trans hI.rdi, ha.hdr hI.hdr⟩, hZ⟩
  · rintro p j s hj ⟨σ, O, N, minv, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (dblIter_ok hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 d8 hsl hsl' hc' hN0 hj hI)
      fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨σ, O, N, minv, hI', hZ, hw, hw', hc', hN0⟩, fun _ => trivial⟩

theorem pins1 {α : Type} {Φ : α → State → Prop} {r₁ : Reg} (f₁ : α → BitVec 64)
    (h : ∀ a s, Φ a s → s.gpr r₁ = f₁ a) : Pins Φ [r₁] := fun a _ _ h₁ h₂ r hr => by
  rw [List.mem_singleton.mp hr, h a _ h₁, h a _ h₂]

theorem pins2 {α : Type} {Φ : α → State → Prop} {r₁ r₂ : Reg} (f₁ f₂ : α → BitVec 64)
    (h : ∀ a s, Φ a s → s.gpr r₁ = f₁ a ∧ s.gpr r₂ = f₂ a) : Pins Φ [r₁, r₂] := fun a _ _ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [(h a _ h₁).1, (h a _ h₂).1]
  · rw [(h a _ h₁).2, (h a _ h₂).2]

theorem pins3 {α : Type} {Φ : α → State → Prop} {r₁ r₂ r₃ : Reg} (f₁ f₂ f₃ : α → BitVec 64)
    (h : ∀ a s, Φ a s → s.gpr r₁ = f₁ a ∧ s.gpr r₂ = f₂ a ∧ s.gpr r₃ = f₃ a) : Pins Φ [r₁, r₂, r₃] :=
  fun a _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [(h a _ h₁).1, (h a _ h₂).1]
    · rw [(h a _ h₁).2.1, (h a _ h₂).2.1]
    · rw [(h a _ h₁).2.2, (h a _ h₂).2.2]

/-- The public data of `r2X` and `r2At`: the working space, `n`'s words,
and the prime's workspace's offset and words. -/
structure RXPub where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  wx : Nat

/-- The prime's workspace. -/
abbrev RXPub.ws (p : RXPub) : Ws := ⟨off p.B p.o, slot p.wx 8, p.wx⟩
/-- `R² mod n`'s chunks. -/
abbrev RXPub.K (p : RXPub) : Nat := (p.w + p.wx - 1) / p.wx
/-- `A` after `k` reductions. -/
abbrev RXPub.A (p : RXPub) (k : Nat) : Nat := 64 * (k * p.wx) + 128 * p.wx

/-- The sizes' bounds. -/
def RXB (p : RXPub) : Prop := 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ p.w < 2 ^ 20

/-- At `r2X`'s start. -/
def RXPre (p : RXPub) (s : State) : Prop :=
  ∃ mx X, SubCtx s p.B p.Z p.o p.w p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧ RXB p ∧
    wv s.mem (off p.B p.o) (slot p.wx aY) p.wx < X

/-- From `fixStart` on, after `k` reductions. -/
def RXK (p : RXPub) (k : Nat) (t : State) : Prop :=
  ∃ σ mx X, FInv False σ t p.B p.Z p.o p.w p.wx mx X k ∧ 1 < X ∧ X % 2 = 1 ∧ RXB p

/-- After the reduction of a step. -/
def RXM (p : RXPub) (k : Nat) (t : State) : Prop :=
  ∃ σ mx X, FMid False σ t p.B p.Z p.o p.w p.wx mx X k ∧ 1 < X ∧ X % 2 = 1 ∧ RXB p

section
variable {p : RXPub} {s t : State} {rs : List Reg} {k : Nat}

theorem RXPre.step (h : RXPre p s) (hm : t.mem = s.mem) (k' : Keep rs s t) (hdi : .rdi ∉ rs) : RXPre p t := by
  obtain ⟨mx, X, hc, hv, h1, h2, hb, hy⟩ := h
  exact ⟨mx, X, hc.of_frm (rs := []) (by rw [hm]; exact fun _ _ => rfl) (by simp) k'.2.2 (k'.gpr hdi),
    ⟨by rw [hm]; exact hv.n, by rw [hm]; exact hv.inv, by rw [hm]; exact hv.one⟩, h1, h2, hb, by rw [hm]; exact hy⟩

theorem RXK.step (h : RXK p k s) (hm : t.mem = s.mem) (k' : Keep rs s t) (hrs : ∀ r ∈ rs, r ∈ mmRegs)
    (hdi : .rdi ∉ rs) : RXK p k t :=
  let ⟨σ, mx, X, hI, h1, h2, hb⟩ := h; ⟨σ, mx, X, hI.step hm k' hrs hdi, h1, h2, hb⟩

theorem RXM.step (h : RXM p k s) (hm : t.mem = s.mem) (k' : Keep rs s t) (hrs : ∀ r ∈ rs, r ∈ mmRegs)
    (hdi : .rdi ∉ rs) : RXM p k t :=
  let ⟨σ, mx, X, hI, h1, h2, hb⟩ := h; ⟨σ, mx, X, hI.step hm k' hrs hdi, h1, h2, hb⟩

theorem RXPre.rdi (h : RXPre p s) : s.gpr .rdi = off p.B p.o := let ⟨_, _, hc, _⟩ := h; hc.rdi
theorem RXK.rdi (h : RXK p k s) : s.gpr .rdi = off p.B p.o := let ⟨_, _, _, hI, _⟩ := h; hI.c.rdi
theorem RXM.rdi (h : RXM p k s) : s.gpr .rdi = off p.B p.o := let ⟨_, _, _, hI, _⟩ := h; hI.c.rdi

theorem RXK.good (h : RXK p k s) : GoodW p.ws s := let ⟨_, mx, _, hI, _⟩ := h; ⟨mx, hI.c.good, Nat.le_refl _⟩

theorem RXK.bnd (h : RXK p k s) : RXB p := let ⟨_, _, _, _, _, _, hb⟩ := h; hb

end

/-! ## The chunks -/

/-- After `chunkWords`' blocks. -/
def XC1 (p : RXPub) (t : State) : Prop := RXPre p t ∧ t.gpr .rax = BitVec.ofNat 64 p.wx ∧ t.gpr .r12 = p.B
def XC2 (p : RXPub) (t : State) : Prop := RXPre p t ∧ t.gpr .rax = BitVec.ofNat 64 p.wx ∧
  t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rcx = BitVec.ofNat 64 0
def XC3 (p : RXPub) (t : State) : Prop := RXPre p t ∧ t.gpr .rax = BitVec.ofNat 64 p.wx ∧
  t.gpr .rcx = BitVec.ofNat 64 (p.K * p.wx)

theorem chunk_ct : RelCT isa (Two RXPre) (seqs chunkWords) (Two XC3) := by
  simp only [chunkWords, seqs]
  refine RelCT.seq (two_piece (Ψ := XC1) [.rdi] (pins1 (fun p => off p.B p.o) fun _ _ h => h.rdi) (by taint_decide)
    ?_) (RelCT.seq (two_piece (Ψ := XC2) [.rdi, .r12] (pins2 (fun p => off p.B p.o) (fun p => p.B)
      fun _ _ h => ⟨h.1.rdi, h.2.2⟩) (by taint_decide) ?_)
    (two_post (two_taint [.rax, .r12, .rcx] (pins3 (fun p => BitVec.ofNat 64 p.wx) (fun p => BitVec.ofNat 64 p.w)
      (fun _ => BitVec.ofNat 64 0) fun _ _ h => h.2) (by taint_decide)) ?_))
  · intro p s h
    obtain ⟨_, _, hc, -⟩ := id h
    exact WP.mono (chunkA_ok hc) fun t ⟨h1, h2, hm, k⟩ => ⟨h.step hm k (by decide), h1, h2⟩
  · rintro p s ⟨h, h1, h2⟩
    obtain ⟨_, _, hc, -⟩ := id h
    exact WP.mono (chunkB_ok hc h2) fun t ⟨h3, h4, hm, k⟩ =>
      ⟨h.step hm k (by decide), (k.gpr (by decide)).trans h1, h3, h4⟩
  · rintro p s ⟨h, h1, h2, h3⟩
    obtain ⟨_, _, _, _, _, _, ⟨hb1, hb2, hb3⟩, _⟩ := id h
    exact WP.mono (kLoop_ok (by omega) (by omega) (by omega) h1 h2 h3) fun t ⟨hcx, hm, k⟩ =>
      ⟨h.step hm k (by decide), (k.gpr (by decide)).trans h1, hcx⟩

/-! ## `fixStart` -/

def S1 (p : RXPub) (t : State) : Prop := RXPre p t ∧ t.gpr .rcx = BitVec.ofNat 64 (p.A p.K) ∧ t.gpr .r12 = p.B
def F0 (p : RXPub) (t : State) : Prop := RXK p p.K t ∧ t.cf = some (decide (p.A p.K < 128 * p.w))

theorem fs_ct : RelCT isa (Two XC3) (seqs fixStart) (Two F0) := by
  simp only [fixStart, seqs]
  refine RelCT.seq (two_piece (Ψ := S1) [.rdi] (pins1 (fun p => off p.B p.o) fun _ _ h => h.1.rdi)
    (by taint_decide) ?_) (two_piece [.rdi, .r12] (pins2 (fun p => off p.B p.o) (fun p => p.B)
      fun _ _ h => ⟨h.1.rdi, h.2.2⟩) (by taint_decide) ?_)
  · rintro p s ⟨h, h1, h2⟩
    obtain ⟨_, _, hc, -⟩ := id h
    exact WP.mono (fsA_ok hc h2 h1) fun t ⟨h3, h4, hm, k⟩ => ⟨h.step hm k (by decide), h3, h4⟩
  · rintro p s ⟨h, h1, h2⟩
    obtain ⟨mx, X, hc, hv, hX1, hXo, ⟨hb1, hb2, hb3⟩, hy⟩ := h
    obtain ⟨hK1, hK2⟩ := kBounds (w := p.w) (show 1 ≤ p.wx by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega)
    exact WP.mono (fsB_ok hc h2 h1 (by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega) hb3) fun t ⟨hm, hcf, k⟩ =>
      ⟨⟨s, mx, X, finv_store (Pr := False) hc hv (by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega) hy (fun h => h.elim) hm k (by decide) (by decide),
        hX1, hXo, hb1, hb2, hb3⟩, hcf⟩

/-! ## The extra reductions -/

/-- After the extra reductions: `128 w ≤ A`. -/
def G (q : RXPub × Nat) (t : State) : Prop := RXK q.1 q.2 t ∧ 128 * q.1.w ≤ q.1.A q.2 ∧ q.1.A q.2 < 2 ^ 30

def Bpre (n : Nat) (q : RXPub × Nat) (s : State) : Prop :=
  n = 128 * q.1.w - q.1.A q.2 ∧ q.1.A q.2 < 128 * q.1.w ∧ RXK q.1 q.2 s
def Mpre (n : Nat) (q : RXPub × Nat) (s : State) : Prop :=
  n = 128 * q.1.w - q.1.A q.2 ∧ q.1.A q.2 < 128 * q.1.w ∧ RXM q.1 q.2 s
def Lpre (n : Nat) (q : RXPub × Nat) (s : State) : Prop := Mpre n q s ∧ s.gpr .r12 = q.1.B
def Bpost (n : Nat) (q : RXPub × Nat) (s : State) : Prop :=
  n = 128 * q.1.w - q.1.A q.2 ∧ q.1.A q.2 < 128 * q.1.w ∧ RXK q.1 (q.2 + 1) s ∧
    s.cf = some (decide (q.1.A (q.2 + 1) < 128 * q.1.w))

theorem body_ct (M : Mont) (n : Nat) :
    RelCT isa (Two (Bpre n)) (.seq (M.mm aY aY aOne) fixStep) (Two (Bpost n)) := by
  refine RelCT.seq (two_post (Ψ := Mpre n) (two_map (fun q => q.1.ws) (fun _ _ h => h.2.2.good)
    (M.ct (by unfold MmUse; decide))) ?_) ?_
  · rintro q s ⟨hn, hA, σ, mx, X, hI, hX1, hXo, ⟨hb1, hb2, hb3⟩⟩
    exact WP.mono (mulY_ok M hI hX1 hb1 hb3 hb2) fun t h => ⟨hn, hA, σ, mx, X, h, hX1, hXo, hb1, hb2, hb3⟩
  unfold fixStep
  refine RelCT.seq (two_piece (Ψ := Lpre n) [.rdi] (pins1 (fun q => off q.1.B q.1.o) fun _ _ h => h.2.2.rdi)
    (by taint_decide) ?_) (two_piece [.rdi, .r12] (pins2 (fun q => off q.1.B q.1.o) (fun q => q.1.B)
      fun _ _ h => ⟨h.1.2.2.rdi, h.2⟩) (by taint_decide) ?_)
  · rintro q s ⟨hn, hA, h⟩
    obtain ⟨_, _, _, hI, -⟩ := id h
    exact WP.mono (link_ok hI.c) fun t ⟨h12, hm, k⟩ => ⟨⟨hn, hA, h.step hm k (by decide) (by decide)⟩, h12⟩
  · rintro q s ⟨⟨hn, hA, σ, mx, X, hI, hX1, hXo, ⟨hb1, hb2, hb3⟩⟩, h12⟩
    exact WP.mono (stepFin_ok hI h12 (by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega) hb3 hA) fun t ⟨hI', hcf⟩ =>
      ⟨hn, hA, ⟨σ, mx, X, hI', hX1, hXo, hb1, hb2, hb3⟩, hcf⟩

theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := by simp [eval, h]
theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := by simp [eval, h]

theorem extra_ct (M : Mont) :
    RelCT isa (Two F0) (.ite .b (.loop (.seq (M.mm aY aY aOne) fixStep) .b) (.block [])) (Two G) := by
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_b h₁.2, eval_b h₂.2]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, ⟨h₁, e₁⟩, ⟨h₂, _⟩⟩ x₁ x₂
    have hlt : p.A p.K < 128 * p.w := by
      have := (eval_b h₁.2).symm.trans e₁; simpa using this
    refine RelCT.loop (fun n s₁ s₂ => ∃ q : RXPub × Nat, Bpre n q s₁ ∧ Bpre n q s₂) (fun n => ?_)
      (128 * p.w - p.A p.K) s₁ s₂ t₁ t₂ s₁' s₂' ⟨(p, p.K), ⟨rfl, hlt, h₁.1⟩, ⟨rfl, hlt, h₂.1⟩⟩ x₁ x₂
    refine (body_ct M n).mono (fun _ _ ⟨q, b₁, b₂⟩ => ⟨q, b₁, b₂⟩) ?_
    rintro u₁ u₂ ⟨q, ⟨hn, hA, k₁, c₁⟩, ⟨-, -, k₂, c₂⟩⟩
    have hb := k₁.bnd
    obtain ⟨hb1, -, hb3⟩ := hb
    have e1 := Nat.add_one_mul q.2 q.1.wx
    refine ⟨by rw [eval_b c₁, eval_b c₂], fun hf => ?_, fun ht => ?_⟩
    · have : ¬ q.1.A (q.2 + 1) < 128 * q.1.w := by
        have := (eval_b c₁).symm.trans hf; simpa using this
      exact ⟨(q.1, q.2 + 1), ⟨k₁, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega⟩, ⟨k₂, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega⟩⟩
    · have hlt' : q.1.A (q.2 + 1) < 128 * q.1.w := by
        have := (eval_b c₁).symm.trans ht; simpa using this
      exact ⟨128 * q.1.w - q.1.A (q.2 + 1), by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega, (q.1, q.2 + 1), ⟨rfl, hlt', k₁⟩, ⟨rfl, hlt', k₂⟩⟩
  · refine (two_post (Ψ := fun p s => G (p, p.K) s) (two_taint [] (fun _ _ _ _ _ _ h => by simp at h)
      (by taint_decide)) fun p s ⟨⟨h, hcf⟩, he⟩ => WP.block_nil ⟨h, ?_⟩).mono (fun _ _ h => h)
      fun _ _ ⟨p, h₁, h₂⟩ => ⟨(p, p.K), h₁, h₂⟩
    have : ¬ p.A p.K < 128 * p.w := by
      have := (eval_b hcf).symm.trans he; simpa using this
    obtain ⟨hb1, hb2, hb3⟩ := h.bnd
    obtain ⟨hK1, hK2⟩ := kBounds (w := p.w) (show 1 ≤ p.wx by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega)
    exact ⟨by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega⟩

/-! ## The doublings -/

def G1 (q : RXPub × Nat) (t : State) : Prop := G q t ∧ t.gpr .rcx = BitVec.ofNat 64 (q.1.A q.2) ∧ t.gpr .r12 = q.1.B
def G2 (q : RXPub × Nat) (t : State) : Prop :=
  G q t ∧ t.gpr .rcx = BitVec.ofNat 64 (q.1.A q.2 - 128 * q.1.w) ∧ t.zf = some (decide (q.1.A q.2 = 128 * q.1.w))

theorem sub_ct : RelCT isa (Two G) (seqs fixSub) (Two G2) := by
  simp only [fixSub, seqs]
  refine RelCT.seq (two_piece (Ψ := G1) [.rdi] (pins1 (fun q => off q.1.B q.1.o) fun _ _ h => h.1.rdi)
    (by taint_decide) ?_) (two_piece [.rdi, .r12] (pins2 (fun q => off q.1.B q.1.o) (fun q => q.1.B)
      fun _ _ h => ⟨h.1.1.rdi, h.2.2⟩) (by taint_decide) ?_)
  · rintro q s ⟨h, h1, h2⟩
    obtain ⟨_, _, _, hI, -⟩ := id h
    exact WP.mono (subA_ok hI.c hI.d) fun t ⟨h3, h4, hm, k⟩ =>
      ⟨⟨h.step hm k (by decide) (by decide), h1, h2⟩, h3, h4⟩
  · rintro q s ⟨⟨h, h1, h2⟩, h3, h4⟩
    obtain ⟨_, _, _, hI, _, _, -, -, hb3⟩ := id h
    exact WP.mono (subB_ok hI.c h4 h3 (by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega) h1 hb3) fun t ⟨h5, h6, hm, k⟩ =>
      ⟨⟨h.step hm k (by decide) (by decide), h1, h2⟩, h5, h6⟩

theorem dbl_ct : RelCT isa (Two G2) (.ite .e (.block []) (doubles aN aAcc aTmp aY sRem)) fun _ _ => True := by
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_e h₁.2.2, eval_e h₂.2.2]) (two_taint [] (fun _ _ _ _ _ _ h => by
    simp at h) (by taint_decide)) ?_
  refine two_map (fun q => (⟨q.1.ws, q.1.A q.2 - 128 * q.1.w⟩ : DblPubW)) (fun q s ⟨⟨⟨h, h1, h2⟩, h3, h4⟩, he⟩ => ?_)
    (doubles_ctW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (sl := sRem) (by decide) (by decide) (by taint_decide)
      (by taint_decide) (by taint_decide))
  have hne : q.1.A q.2 ≠ 128 * q.1.w := by
    have := (eval_e h4).symm.trans he; simpa using this
  obtain ⟨_, mx, _, hI, _, _, hb1, -, -⟩ := h
  exact ⟨mx, ⟨hI.c.good, Nat.le_refl _⟩, hb1, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega, h3, by rw [hI.v.n]; exact hI.lt⟩

/-- `r2X` leaks the same in runs with the same workspaces. -/
theorem r2X_ct (M : Mont) : RelCT isa (Two RXPre) (seqs (r2X M.mm)) fun _ _ => True := by
  unfold r2X
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp [chunkWords]) (by simp [fixStart]) (RelCT.seq chunk_ct ?_)
  refine RelCT.seqs_append (by simp [fixStart]) (by simp) (RelCT.seq fs_ct ?_)
  refine RelCT.seqs_append (by simp) (by simp [fixSub]) (RelCT.seq (extra_ct M) ?_)
  exact RelCT.seqs_append (by simp [fixSub]) (by simp) (RelCT.seq sub_ct dbl_ct)

/-! ## `r2At` -/

/-- `r2At_ok`'s hypotheses. -/
def APre (sl : Nat) (p : RXPub) (s : State) : Prop :=
  ∃ (minv mx : BitVec 64) (X : Nat), Good s p.B p.Z p.w minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 20 ∧ slot p.w 8 ≤ p.o ∧
    p.o + slot p.wx 8 + wsTab p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧ word s.mem p.B (8 * sl) = off p.B p.o ∧
    WsAt s.mem p.B p.o p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1

/-- In the prime's workspace. -/
def E1 (p : RXPub) (s : State) : Prop :=
  ∃ mx X, SubCtx s p.B p.Z p.o p.w p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧ RXB p
/-- After the reduction of `R² mod n`. -/
def E2 (p : RXPub) (s : State) : Prop :=
  ∃ mx X, SubCtx s p.B p.Z p.o p.w p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧ RXB p ∧
    wv s.mem (off p.B p.o) (slot p.wx aXc) p.wx < X

/-- The workspace as `redc` sees it. -/
abbrev RXPub.xp (p : RXPub) : XPub := ⟨p.B, p.Z, p.o, p.w, p.wx⟩

/-- `r2At sl` leaks the same in runs with the same workspaces, given that the
taint analysis checks its load of the prime's workspace. -/
theorem r2At_ct (M : Mont) {sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    RelCT isa (Two (APre sl)) (seqs (r2At M.mm sl)) fun _ _ => True := by
  unfold r2At
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [redc]) (RelCT.seq (two_piece (Ψ := E1) [.rdi]
    (pins1 (fun p => p.B) fun _ _ ⟨_, _, _, hg, _⟩ => hg.rdi) hT ?_) ?_)
  · rintro p s ⟨minv, mx, X, hg, hw8, hw20, hlo, hhi, hwx2, hwxw, hsl, hslv, hws, hX, hX1, hXo⟩
    have hs := hg.scr
    have := hdr_lt_slot p.w 8 (show sl < 32 from hsl)
    refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.B p.o ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl) fun t ⟨⟨hdi, hm⟩, k⟩ =>
      ⟨mx, X, SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr) (by rw [hm]; exact hws) hdi hlo
        (hi_of_wsTab hhi), ⟨by rw [hm]; exact hX.n, by rw [hm]; exact hX.inv, by rw [hm]; exact hX.one⟩, hX1, hXo,
        hwx2, hwxw, hw20⟩
  refine RelCT.seqs_append (by simp [redc]) (by simp [copyArr]) (RelCT.seq (two_post (Ψ := E2)
    (two_map RXPub.xp (fun p _ ⟨mx, X, hc, hv, hX1, _, hb1, hb2, hb3⟩ => ⟨mx, X, hc, hv, hb1, hb2, show p.w < 2 ^ 30 by omega, hX1,
      by decide⟩) (redc_ct_of M (j := aR2) (by taint_decide))) ?_) ?_)
  · rintro p s ⟨mx, X, hc, hv, hX1, hXo, hb1, hb2, hb3⟩
    exact WP.mono (redc_ok M hc hv hb1 hb2 (by omega) hX1 (j := aR2) (by decide)) fun t ⟨hc', hv', hlt, _⟩ =>
      ⟨mx, X, hc', hv', hX1, hXo, ⟨hb1, hb2, hb3⟩, hlt⟩
  refine RelCT.seqs_append (by simp [copyArr]) (by simp [r2X]) (RelCT.seq (two_post (Ψ := RXPre)
    (two_map RXPub.ws (fun _ _ ⟨mx, _, hc, _⟩ => ⟨mx, hc.good, Nat.le_refl _⟩)
      (copyArr_ct (o := aY) (a := aXc) (by decide) (by decide) (by taint_decide))) ?_) ?_)
  · rintro p s ⟨mx, X, hc, hv, hX1, hXo, ⟨hb1, hb2, hb3⟩, hlt⟩
    have hn := hc.good.scr.nowrap
    exact WP.mono (copyArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) (o := aY) (a := aXc)
      (by decide) (by decide) (by decide)) fun t ⟨hv₃, ho₃, k₃⟩ => by
        have f₃ : Frm (off p.B p.o) (r2Ranges p.wx) s.mem t.mem :=
          Frm.of_outside (ho₃.mono (o' := slot p.wx aY) (n' := 8 * (p.wx + 2)) (Nat.le_refl _) (by omega))
            (by simp [r2Ranges])
        exact ⟨mx, X, hc.of_frm f₃ (r2Ranges_ok p.wx) k₃.2.2 (k₃.gpr (by decide)), xvals_r2 hv hn (by omega) f₃,
          hX1, hXo, ⟨hb1, hb2, hb3⟩, by rw [hv₃]; exact hlt⟩
  refine RelCT.seqs_append (by simp [r2X]) (by simp) (RelCT.seq (two_post (Ψ := fun p t =>
    t.gpr .rdi = off p.B p.o) (r2X_ct M) ?_) (two_taint [.rdi] (pins1 (fun p => off p.B p.o) fun _ _ h => h)
      (by taint_decide)))
  rintro p s ⟨mx, X, hc, hv, hX1, hXo, ⟨hb1, hb2, hb3⟩, hy⟩
  exact WP.mono (r2X_ok M (Pr := False) hc hv hX1 hXo hb1 hb2 hb3 hy (fun h => h.elim)) fun _ h => h.1.rdi

end VG.Proof.Bignum.X86_64.PrivPre
