import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub

/-!
# RSA with AVX512_IFMA on x86-64: constant time, lemmas

What the constant-time proofs of `CrtIfma` (`CT*.lean`) use: a block
checked by the taint analysis after loads whose results correctness gives
(`ct_split`), pins from equations (`pins_eqs`), `doubles` in a prime's
workspace (`doublesW_ct`), and the moves between the workspaces (`swap_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## Helpers -/

/-- A block whose first instructions load what the rest's addresses need. -/
theorem ct_split {α : Type} {Φ Ψ : α → State → Prop} (l₁ l₂ : List Instr) (rs₁ rs₂ : List Reg)
    (hp₁ : Pins Φ rs₁) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (h₁ : (taint.check (Taint.ofRegs rs₁) (.block l₁) hc₁).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block l₁) s (Ψ a)) (hp₂ : Pins Ψ rs₂) {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (h₂ : (taint.check (Taint.ofRegs rs₂) (.block l₂) hc₂).isSome = true) :
    RelCT isa (Two Φ) (.block (l₁ ++ l₂)) fun _ _ => True :=
  RelCT.block_append (RelCT.seq (two_piece rs₁ hp₁ h₁ hw) (two_taint rs₂ hp₂ h₂))

/-- Pins from equalities to functions of the public data. -/
theorem pins_eqs {α : Type} {Φ : α → State → Prop} {rs : List Reg} (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs := pins_of f h

/-! ## `doubles` in a prime's workspace -/

/-- `double` leaks the same in runs with the same working space (whatever `-m⁻¹`). -/
theorem doubleW_ct {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true) :
    RelCT isa (Two GoodW) (double mo acc tmp o) fun _ _ => True :=
  RelCT.seq (two_piece (Ψ := fun (L : Ws) t => DblHeadL mo acc tmp o ⟨L.B, L.Z, L.w, 0⟩ t) _ pins_goodW h
      fun L s ⟨minv, hg, hZ⟩ => dblHead_ok (L := ⟨L.B, L.Z, L.w, minv⟩) ⟨hg, hZ⟩ hmo hacc htmp ho)
    (two_taint _ (fun L s₁ s₂ h₁ h₂ => pins_dblHead mo acc tmp o _ s₁ s₂ h₁ h₂) (by taint_decide))

/-- What `doubles` keeps after `j` doublings, for some `-m⁻¹`. -/
def DblsAtW (mo acc tmp o sl : Nat) (p : Ws × Nat) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (minv : BitVec 64) (O N : Nat), DblsInv σ p.1.B p.1.Z p.1.w minv mo acc tmp o sl p.2 O N j t ∧
    slot p.1.w 8 ≤ p.1.Z ∧ 2 ≤ p.1.w ∧ p.1.w < 2 ^ 31 ∧ p.2 < 2 ^ 31 ∧ 0 < N

/-- What `doubles` needs: the working space, the count in `rcx`, and `[o] < [mo]`. -/
def DblPreW (mo o : Nat) (p : Ws × Nat) (s : State) : Prop :=
  GoodW p.1 s ∧ 2 ≤ p.1.w ∧ p.1.w < 2 ^ 31 ∧ 1 ≤ p.2 ∧ p.2 < 2 ^ 31 ∧ s.gpr .rcx = BitVec.ofNat 64 p.2 ∧
    wv s.mem p.1.B (slot p.1.w o) p.1.w < wv s.mem p.1.B (slot p.1.w mo) p.1.w

/-- `doubles` leaks the same in runs with the same working space and count. -/
theorem doublesW_ct {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.rdi]) (.block [.store (hdr sl) .rcx]) hc').isSome = true)
    {hc'' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h'' : (taint.check (Taint.ofRegs [.rdi]) (.block (dblCount sl)) hc'').isSome = true) :
    RelCT isa (Two (DblPreW mo o)) (doubles mo acc tmp o sl) fun _ _ => True := by
  rw [doubles_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.2 ∧ DblsAtW mo acc tmp o sl p 0 s) _
    (fun p s₁ s₂ h₁ h₂ => pins_goodW p.1 s₁ s₂ h₁.1 h₂.1) h' ?_) ?_
  · rintro p s ⟨⟨minv, hg, hZ⟩, hw, hw', hc1, hc', hcx, hO⟩
    exact WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hg.scr hg.rdi hg.hdr hZ hmo ho hsl hsl' hcx hO)
      fun t hI => ⟨by omega, s, minv, _, _, hI, hZ, hw, hw', hc', by omega⟩
  refine (two_loop (Φ := DblsAtW mo acc tmp o sl) (Ψ := fun _ _ => True) (fun p => p.2) ?_ ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : (Ws × Nat) × Nat) s => GoodW q.1.1 s)
      (two_map (·.1.1) (fun _ _ h => ?_) (doubleW_ct hmo hacc htmp ho h)) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_goodW q.1.1 s₁ s₂ h₁ h₂) h'')
    · obtain ⟨_, σ, minv, O, N, hI, hZ, _⟩ := h
      exact ⟨minv, ⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩
    rintro ⟨p, j⟩ s ⟨hj, σ, minv, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (double_ok hI.scr hI.rdi hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t ⟨_, ha, k⟩ =>
        ⟨minv, ⟨hI.scr.congr k.2.2, (k.gpr (by decide)).trans hI.rdi, ha.hdr hI.hdr⟩, hZ⟩
  · rintro p j s hj ⟨σ, minv, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (dblIter_ok hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 d8 hsl hsl' hc' hN0 hj hI)
      fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨σ, minv, O, N, hI', hZ, hw, hw', hc', hN0⟩,
        fun _ => trivial⟩

/-! ## `k1`, and the region -/

/-- A piece, then the rest of a list. -/
theorem ct_cons {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} {cs : List (Prog isa)} (hcs : cs ≠ [])
    (hc : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a))
    (hr : RelCT isa (Two Ψ) (seqs cs) fun _ _ => True) : RelCT isa (Two Φ) (seqs (c :: cs)) fun _ _ => True := by
  match cs, hcs with
  | _ :: _, _ => exact ct_step id (fun _ _ h => h) hw hc hr

end VG.Proof.Bignum.X86_64

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## Between the workspaces -/

/-- In a prime's workspace (`rdi = off B o`), linked to `n`'s. -/
def SwPre (p : Addr × Nat × Nat) (s : State) : Prop :=
  Scr s p.1 p.2.2 ∧ s.gpr .rdi = off p.1 p.2.1 ∧ word s.mem (off p.1 p.2.1) (8 * sLink) = p.1 ∧
    p.2.1 + 8 * 32 ≤ p.2.2

/-- Back to `n`'s workspace, and into the one in slot `sl`: constant time. -/
theorem swap_ct (sl : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    RelCT isa (Two SwPre) (.block [leave, .mov .rdi (.mem (hdr sl))]) fun _ _ => True :=
  ct_split [leave] [.mov .rdi (.mem (hdr sl))] [.rdi] [.rdi]
    (pins_eqs (fun p _ => off p.1 p.2.1) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2.1)
    (by taint_decide) (Ψ := fun p t => t.gpr .rdi = p.1)
    (fun p s ⟨hs, hdi, hlk, ho⟩ => WP.mono (leaveB_ok hs hdi hlk ho) fun t h => h.1)
    (pins_eqs (fun p _ => p.1) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h) hT

/-! ## `ifma` -/

theorem swPre_of {B : Addr} {o Z : Nat} {s : State} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B o)
    (hlk : word s.mem (off B o) (8 * sLink) = B) (ho : o + 8 * 32 ≤ Z) : SwPre (B, o, Z) s :=
  ⟨hs, hdi, hlk, ho⟩

end VG.Proof.Bignum.X86_64
