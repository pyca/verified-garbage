module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTLoadPre
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTLoadPre
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: constant time of the offsets in `pre`

The code computing the offset of a value in `pre` (`offN`, `offP`, `offQ`)
is constant time, as `loadPre_ct` needs it. `offP` and `offQ` read `n`'s
header through the prime's workspace's link, and `offQ` `p`'s through
`n`'s, so each load from a loaded pointer is checked with that pointer
public: the bases the code reads (`OffD`) are public data.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `offN`: `R² mod n` at word `w` of `pre`, from `n`'s workspace. -/
theorem offN_ct {α : Type} (π : α → LPub) {j : Nat} {Q : α → State → Prop}
    (hd : ∀ a s, Q a s → (π a).d = (π a).w) :
    RelCT isa (Two fun a s => LpA j (π a) s ∧ Q a s) (.block Crt.offN) (Two (LpB j)) :=
  RelCT.mono (Q := Two fun a => LpB j (π a)) (two_piece [.rdi] (pins_of (fun a _ => (π a).W) fun a s h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.1.1.rdi) (by taint_decide) fun a s ⟨⟨hgd, hsi⟩, hq⟩ => by
    obtain ⟨minv, hg, hZ, -, -, -, -, -⟩ := id hgd
    have hl : InRegions (s.rd ++ s.wr) (off (π a).W (8 * sW)) 8 :=
      hg.scr.ld (by have := hdr_lt_slot (π a).w 8 (show sW < 32 by decide); omega)
    exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (π a).w ∧ t.mem = s.mem)
      (by xrun [Crt.offN, State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.hw]) rfl) fun t ⟨⟨h1, hm⟩, k⟩ =>
      ⟨hgd.congr hm k (by decide), (k.gpr (by decide)).trans hsi, by rw [h1, hd a s hq]⟩) (fun _ _ h => h)
    fun _ _ ⟨a, h₁, h₂⟩ => ⟨π a, h₁, h₂⟩

/-- The bases `offP` and `offQ` read: `n`'s workspace, its length, and
`p`'s workspace (at offset `op`) and length. -/
structure OffD where
  B : Addr
  w : Nat
  op : Nat
  wp : Nat

/-- What `offP` reads: the link to `n`'s workspace and `n`'s length. -/
def OffPF (p : LPub) (D : OffD) (s : State) : Prop :=
  InRegions (s.rd ++ s.wr) (off p.W (8 * sLink)) 8 ∧ word s.mem p.W (8 * sLink) = D.B ∧
    InRegions (s.rd ++ s.wr) (off D.B (8 * sW)) 8 ∧ word s.mem D.B (8 * sW) = BitVec.ofNat 64 D.w

/-- What `offQ` reads: also `p`'s workspace from `n`'s header, and its length. -/
def OffQF (p : LPub) (D : OffD) (s : State) : Prop :=
  OffPF p D s ∧ InRegions (s.rd ++ s.wr) (off D.B (8 * sWsP)) 8 ∧ word s.mem D.B (8 * sWsP) = off D.B D.op ∧
    InRegions (s.rd ++ s.wr) (off (off D.B D.op) (8 * sW)) 8 ∧
    word s.mem (off D.B D.op) (8 * sW) = BitVec.ofNat 64 D.wp

theorem OffPF.congr {p : LPub} {D : OffD} {s t : State} {rs : List Reg} (h : OffPF p D s) (hm : t.mem = s.mem)
    (k : Keep rs s t) : OffPF p D t := by
  obtain ⟨a, b, c, d⟩ := h
  exact ⟨by rw [k.2.1, k.2.2]; exact a, by rw [hm]; exact b, by rw [k.2.1, k.2.2]; exact c, by rw [hm]; exact d⟩

theorem OffQF.congr {p : LPub} {D : OffD} {s t : State} {rs : List Reg} (h : OffQF p D s) (hm : t.mem = s.mem)
    (k : Keep rs s t) : OffQF p D t := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨a.congr hm k, by rw [k.2.1, k.2.2]; exact b, by rw [hm]; exact c, by rw [k.2.1, k.2.2]; exact d,
    by rw [hm]; exact e⟩

/-- After `offP`'s first load: `n`'s base in `rax`. -/
def OffP1 (j : Nat) (F : LPub → OffD → State → Prop) (p : LPub × OffD) (s : State) : Prop :=
  LpA j p.1 s ∧ F p.1 p.2 s ∧ s.gpr .rax = p.2.B

/-- `offP`'s first load. -/
theorem offLink_ct {α : Type} (π : α → LPub) (δ : α → OffD) {j : Nat} {Q : α → State → Prop}
    {F : LPub → OffD → State → Prop} (hF : ∀ a s, Q a s → F (π a) (δ a) s)
    (hFp : ∀ p D s, F p D s → OffPF p D s)
    (hFk : ∀ p D s t, F p D s → t.mem = s.mem → Keep [.rax] s t → F p D t) :
    RelCT isa (Two fun a s => LpA j (π a) s ∧ Q a s) (.block [.mov .rax (.mem (hdr sLink))])
      (Two (OffP1 j F)) :=
  RelCT.mono (Q := Two fun a => OffP1 j F (π a, δ a)) (two_piece [.rdi] (pins_of (fun a _ => (π a).W) fun a s h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.1.1.rdi) (by taint_decide) fun a s ⟨⟨hgd, hsi⟩, hq⟩ => by
    have hf := hF a s hq
    obtain ⟨hl, hlk, -, -⟩ := hFp _ _ _ hf
    exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = (δ a).B ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hgd.rdi, hdrOff, hl, hlk]) rfl) fun t ⟨⟨h1, hm⟩, k⟩ =>
      ⟨⟨hgd.congr hm k (by decide), (k.gpr (by decide)).trans hsi⟩, hFk _ _ _ _ hf hm k, h1⟩)
    (fun _ _ h => h) fun _ _ ⟨a, h₁, h₂⟩ => ⟨(π a, δ a), h₁, h₂⟩

/-- `offP`: `R_p mod p` at word `2 w` of `pre`, from a prime's workspace. -/
theorem offP_ct {α : Type} (π : α → LPub) (δ : α → OffD) {j : Nat} {Q : α → State → Prop}
    (hF : ∀ a s, Q a s → OffPF (π a) (δ a) s) (hd : ∀ a, (π a).d = 2 * (δ a).w) :
    RelCT isa (Two fun a s => LpA j (π a) s ∧ Q a s) (.block Crt.offP) (Two (LpB j)) := by
  rw [show Crt.offP = ([.mov .rax (.mem (hdr sLink))] : List Instr) ++
    [.mov .rax (.mem (Crt.ws .rax sW)), .alu .add .rax (.reg .rax)] from rfl]
  refine RelCT.block_append (RelCT.seq (offLink_ct π δ (F := fun p D s => OffPF p D s ∧ p.d = 2 * D.w)
    (fun a s h => ⟨hF a s h, hd a⟩) (fun _ _ _ h => h.1) fun _ _ _ _ h hm k => ⟨h.1.congr hm k, h.2⟩) ?_)
  refine RelCT.mono (two_piece (Φ := OffP1 j fun p D s => OffPF p D s ∧ p.d = 2 * D.w)
    (Ψ := fun p => LpB j p.1) [.rax] (pins_of (fun p _ => p.2.B) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2) (by taint_decide) ?_)
    (fun _ _ h => h) fun _ _ ⟨p, h₁, h₂⟩ => ⟨p.1, h₁, h₂⟩
  rintro ⟨p, D⟩ s ⟨⟨hgd, hsi⟩, ⟨⟨-, -, hl, hw⟩, hdw⟩, hax⟩
  exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (2 * D.w) ∧ t.mem = s.mem)
    (by xrun [State.ea, Crt.ws, hax, hdrOff, hl, hw, Nat.two_mul, BitVec.ofNat_add]) rfl) fun t ⟨⟨h1, hm⟩, k⟩ =>
    ⟨hgd.congr hm k (by decide), (k.gpr (by decide)).trans hsi, by rw [h1, hdw]⟩

/-- In `offQ`, after `2 w`: `n`'s base in `rdx`. -/
def OffQ2 (j : Nat) (F : LPub → OffD → State → Prop) (p : LPub × OffD) (s : State) : Prop :=
  LpA j p.1 s ∧ F p.1 p.2 s ∧ s.gpr .rax = BitVec.ofNat 64 (2 * p.2.w) ∧ s.gpr .rdx = p.2.B

/-- In `offQ`, after the load of `p`'s base into `rdx`. -/
def OffQ3 (j : Nat) (F : LPub → OffD → State → Prop) (p : LPub × OffD) (s : State) : Prop :=
  LpA j p.1 s ∧ F p.1 p.2 s ∧ s.gpr .rax = BitVec.ofNat 64 (2 * p.2.w) ∧ s.gpr .rdx = off p.2.B p.2.op

/-- `offQ`: `R_q mod q` at word `2 w + w_p` of `pre`, from a prime's workspace. -/
theorem offQ_ct {α : Type} (π : α → LPub) (δ : α → OffD) {j : Nat} {Q : α → State → Prop}
    (hF : ∀ a s, Q a s → OffQF (π a) (δ a) s) (hd : ∀ a, (π a).d = 2 * (δ a).w + (δ a).wp) :
    RelCT isa (Two fun a s => LpA j (π a) s ∧ Q a s) (.block Crt.offQ) (Two (LpB j)) := by
  rw [show Crt.offQ = ([.mov .rax (.mem (hdr sLink))] : List Instr) ++
    (([.mov .rax (.mem (Crt.ws .rax sW)), .alu .add .rax (.reg .rax), .mov .rdx (.mem (hdr sLink))] : List Instr) ++
      (([.mov .rdx (.mem (Crt.ws .rdx sWsP))] : List Instr) ++ [.alu .add .rax (.mem (Crt.ws .rdx sW))])) from rfl]
  let F : LPub → OffD → State → Prop := fun p D s => OffQF p D s ∧ p.d = 2 * D.w + D.wp
  have hFk : ∀ p D s t, F p D s → t.mem = s.mem → ∀ {rs : List Reg}, Keep rs s t → F p D t :=
    fun _ _ _ _ h hm _ k => ⟨h.1.congr hm k, h.2⟩
  refine RelCT.block_append (RelCT.seq (offLink_ct π δ (F := F) (fun a s h => ⟨hF a s h, hd a⟩)
    (fun _ _ _ h => h.1.1) fun _ _ _ _ h hm k => hFk _ _ _ _ h hm k) ?_)
  refine RelCT.block_append (RelCT.seq (two_piece (Φ := OffP1 j F) (Ψ := OffQ2 j F) [.rax, .rdi]
    (pins_of (fun p r => if r = .rax then p.2.B else p.1.W) fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.2.2
      · exact h.1.1.rdi) (by taint_decide) ?_) ?_)
  · rintro ⟨p, D⟩ s ⟨⟨hgd, hsi⟩, hf, hax⟩
    obtain ⟨⟨⟨hl1, hlk, hl2, hw⟩, -⟩, -⟩ := id hf
    exact WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (2 * D.w) ∧
        t.gpr .rdx = D.B ∧ t.mem = s.mem)
      (by xrun [State.ea, Crt.ws, hdr, hgd.rdi, hax, hdrOff, hl1, hlk, hl2, hw, Nat.two_mul, BitVec.ofNat_add]) rfl)
      fun t ⟨⟨h1, h2, hm⟩, k⟩ => ⟨⟨hgd.congr hm k (by decide), (k.gpr (by decide)).trans hsi⟩, hFk _ _ _ _ hf hm k,
        h1, h2⟩
  refine RelCT.block_append (RelCT.seq (two_piece (Φ := OffQ2 j F) (Ψ := OffQ3 j F) [.rdx]
    (pins_of (fun p _ => p.2.B) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.2) (by taint_decide) ?_) ?_)
  · rintro ⟨p, D⟩ s ⟨⟨hgd, hsi⟩, hf, hax, hdx⟩
    obtain ⟨⟨-, hl3, hp, -, -⟩, -⟩ := id hf
    exact WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = off D.B D.op ∧ t.mem = s.mem)
      (by xrun [State.ea, Crt.ws, hdx, hdrOff, hl3, hp]) rfl)
      fun t ⟨⟨h2, hm⟩, k⟩ => ⟨⟨hgd.congr hm k (by decide), (k.gpr (by decide)).trans hsi⟩, hFk _ _ _ _ hf hm k,
        (k.gpr (by decide)).trans hax, h2⟩
  refine RelCT.mono (two_piece (Φ := OffQ3 j F) (Ψ := fun p => LpB j p.1) [.rdx]
    (pins_of (fun p _ => off p.2.B p.2.op) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.2) (by taint_decide) ?_)
    (fun _ _ h => h) fun _ _ ⟨p, h₁, h₂⟩ => ⟨p.1, h₁, h₂⟩
  rintro ⟨p, D⟩ s ⟨⟨hgd, hsi⟩, ⟨⟨-, -, -, hl4, hwp⟩, hdw⟩, hax, hdx⟩
  exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (2 * D.w + D.wp) ∧ t.mem = s.mem)
    (by xrun [State.ea, Crt.ws, hdx, hax, hdrOff, hl4, hwp, BitVec.ofNat_add]) rfl) fun t ⟨⟨h1, hm⟩, k⟩ =>
    ⟨hgd.congr hm k (by decide), (k.gpr (by decide)).trans hsi, by rw [h1, hdw]⟩

end VG.Proof.Bignum.X86_64
