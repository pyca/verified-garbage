module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_rsa_private_crt` on x86-64: constant time but for `n`

`entry` and the modulus' check leak the same in runs that agree on the
public data (the arguments but the input and the key's values, and `n`),
and so do `fail` and `main` (`crtMain_ct`): `crtCode_ct`, and the contract's
`ConstantTime` (`crtCode_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `vg_rsa_private_crt`: `main`'s and the stack pointer. -/
structure CCPub where
  m : CrtPub
  rsp : Addr

/-- The arguments of a state with the public data `p`. -/
abbrev CCEq (p : CCPub) (s : State) : Prop :=
  s.gpr .rsp = p.rsp ∧ stackArg s 10 = p.m.B ∧ (stackArg s 11).toNat * 8 = p.m.Z ∧
    (s.gpr .rcx).toNat = p.m.k ∧ s.gpr .rdi = p.m.op ∧ s.gpr .rdx = p.m.np ∧ s.gpr .r8 = p.m.ip ∧
    stackArg s 0 = p.m.pp ∧ stackArg s 2 = p.m.qp ∧ stackArg s 4 = p.m.dpp ∧ stackArg s 6 = p.m.dqp ∧
    stackArg s 8 = p.m.qip ∧ (stackArg s 1).toNat = p.m.pl ∧ (stackArg s 3).toNat = p.m.ql ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = p.m.nb

/-- What the entry and the modulus' check use of a relation `Rel` between
the public data and the states it allows (`crtEntryWith_ct`). -/
abbrev CCOk {α : Type} (f : α → CCPub) (Rel : α → State → Prop) : Prop := ∀ p s, Rel p s → CrtCtx s ∧ CCEq (f p) s

theorem crtEntry_split : Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) =
    ([.mov .r11 (.mem { base := .rsp, disp := 88 })] : List Instr) ++
      ((Crt.entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) := rfl

/-- After `entry`'s first instruction, from a state `Rel` allows. -/
def CC1W {α : Type} (f : α → CCPub) (Rel : α → State → Prop) (p : α) (t : State) : Prop :=
  ∃ s, Rel p s ∧ t.gpr .r11 = (f p).m.B ∧ t.gpr .rsp = (f p).rsp ∧
    WP isa (.block ((Crt.entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))])) t
      (CrtHeadPost s)

/-- After `entry` and the reloads. -/
def CC2W {α : Type} (Rel : α → State → Prop) (p : α) (t : State) : Prop := ∃ s, Rel p s ∧ CrtHeadPost s t

/-- After the modulus' check. -/
def CC3W {α : Type} (f : α → CCPub) (Rel : α → State → Prop) (p : α) (t : State) : Prop :=
  ∃ s t₁, Rel p s ∧ CrtHeadPost s t₁ ∧ t.mem = t₁.mem ∧ Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid (f p).m.N (f p).m.k)

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem cc3W_pre {α : Type} {f : α → CCPub} {Rel : α → State → Prop} (hR : CCOk f Rel) {p : α} {t : State} (h : CC3W f Rel p t) :
    ∃ xb pb qb dpb dqb qib, CrtPre t (f p).m.B (f p).m.Z (f p).m.k (f p).m.op (f p).m.np (f p).m.ip (f p).m.pp (f p).m.qp (f p).m.dpp (f p).m.dqp
      (f p).m.qip (f p).m.pl (f p).m.ql (f p).m.nb xb pb qb dpb dqb qib := by
  obtain ⟨s, t₁, hs, h, hm, k, -⟩ := h
  obtain ⟨c, -, hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql, hnb⟩ := hR p s hs
  have := crtPre_of c h hm k
  rw [hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql] at this
  rw [hnp, hk] at hnb
  rw [hnb] at this
  exact ⟨_, _, _, _, _, _, this⟩

variable (M : Mont) (E : CrtExpL M)

/-- The entry and the modulus' check leak the same in runs from states that
`Rel` allows with the same public data, and so does the rest if `fail` and
`main` do: `vg_rsa_private_crt` and its variants with the key's precomputed
values, by their `main` and the relation of their contract. -/
theorem crtEntryWith_ct {α : Type} {f : α → CCPub} {Rel : α → State → Prop} (hR : CCOk f Rel) (main : Prog isa)
    (hM : RelCT isa (Two fun p t => CC3W f Rel p t ∧ isa.eval .ne t = some false) main fun _ _ => True) :
    RelCT isa (Two Rel) (.seq (.block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] :
      List Instr) ++ invalid)) (.ite .ne fail main)) fun _ _ => True := by
  refine RelCT.seq (R := Two (CC3W f Rel)) (RelCT.block_append (RelCT.seq (R := Two (CC2W Rel)) ?_ ?_)) ?_
  · rw [crtEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CC1W f Rel) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hR p s₁ h₁).2.1, (hR p s₂ h₂).2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    obtain ⟨c, hq⟩ := hR p s hs
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 88 })] : List Instr) ++
        ((Crt.entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]))) s (CrtHeadPost s) := by
      rw [← crtEntry_split]; exact crtHead_ok c
    have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
    have hB' : s.mem.readW (stackArgAddr s 10) 64 = stackArg s 10 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 10)
      (by xrun [State.ea, e10, c.ha 10 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hq.2.1, (k.gpr (by decide)).trans hq.1, hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      have c₁ := (hR p σ₁ c₁).2
      have c₂ := (hR p σ₂ c₂).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx, c₁.2.2.2.2.2.1, c₂.2.2.2.2.2.1]
      · rw [h₁.rcx, h₂.rcx, c₁.2.2.2.1, c₂.2.2.2.1]) (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    obtain ⟨c, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, hn⟩ := hR p s hs
    have hnb := c.hnb.congrK h.inScr h.keep
    refine WP.mono (invalid_ok h.rdx h.rcx c.hk1 c.hk2 (bytesAt_length _ _ _) (fun i hi => hnb.rd i (by
      rw [bytesAt_length]; exact hi)) (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ =>
        ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, hn, hk]
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold fail
    have pin : ∀ p t, (CC3W f Rel p t ∧ isa.eval .ne t = some true) → t.gpr .rdi = (f p).m.B := fun p t ⟨h, _⟩ => by
      obtain ⟨_, _, _, _, _, _, hpre⟩ := cc3W_pre hR h
      exact hpre.rdi
    refine RelCT.seq (two_piece (Ψ := fun (p : α) t => t.gpr .rsi = (f p).m.op ∧
        t.gpr .rcx = BitVec.ofNat 64 (f p).m.k ∧ t.gpr .rdi = (f p).m.B) [.rdi]
      (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [pin p s₁ h₁, pin p s₂ h₂]) (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨_, _, _, _, _, _, hpre⟩ := cc3W_pre hR h
    have hn := hpre.scr.nowrap
    have hk1 := hpre.k1
    have hk2 := hpre.k2
    have hZq := hpre.z
    have h8 := hdr_lt_slot (((f p).m.k + 7) / 8) 8 (show 31 < 32 by decide)
    have hZ : 8 * 32 ≤ (f p).m.Z := by unfold offQ at hZq; omega
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (f p).m.B (8 * i)) 8 := fun i hi => hpre.scr.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = (f p).m.op ∧
        t'.gpr .rcx = BitVec.ofNat 64 (f p).m.k) (by
      xrun [State.ea, hdr, hpre.rdi, hdrOff, hl sOut (by decide), hl sK (by decide), hpre.hO, hpre.hK]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨hsi, hcx, (k'.gpr (by decide)).trans hpre.rdi⟩
  · exact hM

/-- The public data of a state. -/
def ccPubOf (s : State) : CCPub :=
  ⟨⟨stackArg s 10, (stackArg s 11).toNat * 8, (s.gpr .rcx).toNat, s.gpr .rdi, s.gpr .rdx, s.gpr .r8,
    stackArg s 0, stackArg s 2, stackArg s 4, stackArg s 6, stackArg s 8, (stackArg s 1).toNat,
    (stackArg s 3).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat⟩, s.gpr .rsp⟩

end VG.Proof.Bignum.X86_64
