module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.CTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Correct
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Correct
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_precompute` on x86-64: constant time but for `n`

`entry`, `zeroPre` and the modulus' check leak the same in runs that agree
on the public data (the arguments but `p`'s and `q`'s bytes, and `n`), and
so do `fail` and `main` (`main_ct`): `code_ct`, and the contract's
`ConstantTime` (`code_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The public data of `vg_rsa_private_precompute`: `main`'s, the stack
pointer and `pre`'s length. -/
structure PCPub where
  q : PPPub
  rsp : Addr
  rsi : BitVec 64

/-- A state the contract allows, with the public data `P`. -/
def PRel (P : PCPub) (s : State) : Prop :=
  ppContract.pre s ∧ s.gpr .rsp = P.rsp ∧ s.gpr .rsi = P.rsi ∧ (s.gpr .rsi).toNat * 8 = P.q.L8 ∧
    stackArg s 2 = P.q.c.B ∧ (stackArg s 3).toNat * 8 = P.q.c.Z ∧ (s.gpr .rcx).toNat = P.q.c.k ∧
    s.gpr .rdi = P.q.c.op ∧ s.gpr .rdx = P.q.c.np ∧ s.gpr .rdi = P.q.c.ip ∧ s.gpr .r8 = P.q.c.pp ∧
    stackArg s 0 = P.q.c.qp ∧ s.gpr .r8 = P.q.c.dpp ∧ stackArg s 0 = P.q.c.dqp ∧ s.gpr .rdi = P.q.c.qip ∧
    (s.gpr .r9).toNat = P.q.c.pl ∧ (stackArg s 1).toNat = P.q.c.ql ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = P.q.c.nb

theorem entry_split : PrivPre.entry =
    ([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++ PrivPre.entry.drop 1 := rfl

/-- What the rest of the code needs after `entry`. -/
def Cont (s t : State) : Prop :=
  t.gpr .rdi = stackArg s 2 ∧ t.gpr .rsi = s.gpr .rsi ∧ Scr t (stackArg s 2) ((stackArg s 3).toNat * 8) ∧
    word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi ∧
    WP isa PrivPre.zeroPre t fun t₂ => t₂.gpr .rdi = stackArg s 2 ∧
      WP isa (.block [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) t₂ (PPHead s)

/-- After `entry`'s first instruction. -/
def C1 (P : PCPub) (t : State) : Prop :=
  ∃ s, PRel P s ∧ t.gpr .r11 = P.q.c.B ∧ t.gpr .rsp = P.rsp ∧ WP isa (.block (PrivPre.entry.drop 1)) t (Cont s)

/-- After `entry`. -/
def C2 (P : PCPub) (t : State) : Prop := ∃ s, PRel P s ∧ Cont s t

theorem entry_ct : RelCT isa (Two PRel) (.block PrivPre.entry) (Two C2) := by
  rw [entry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := C1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
    (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro P s hs
  have c := ppCtx_of hs.1
  have hZ := c.hZ
  have hk1 := c.hk1
  have hL := c.hL
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords] at hL
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  have hk2 := c.hk2
  have hh : WP isa (.block PrivPre.entry) s (Cont s) :=
    WP.mono (WP.and (head_ok c) (entry_ok c)) fun t ⟨hw, hdi, _, hO, _, _, _, _, _, _, _, _, _, _, _, k⟩ =>
      ⟨hdi, k.gpr (by decide), c.hs.congr k.2.2, hO, WP.mono (WP.and hw (zeroPre_ok (c.hs.congr k.2.2) hdi
        (by omega) (L := (s.gpr .rsi).toNat) (by omega) (by omega)
        (by rw [k.gpr (by decide), ofNat_toNat_self]) hO (fun j hj => by rw [k.2.2]; exact c.hout j hj)))
        fun t₂ ⟨hr, _, _, k₂⟩ => ⟨(k₂.gpr (by decide)).trans hdi, hr⟩⟩
  rw [entry_split, WP.block_append_iff] at hh
  have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
  have hB' : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
  refine WP.mono (WP.and hh (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 2)
    (by xrun [State.ea, e2, c.ha 2 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
      ⟨s, hs, h11.trans hs.2.2.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw⟩

/-- Before `zeroPre`'s loop. -/
def C2b (P : PCPub) (t : State) : Prop :=
  ∃ s, PRel P s ∧ t.gpr .rsi = P.q.c.op ∧ t.gpr .rcx = BitVec.ofNat 64 P.q.L8 ∧ t.gpr .rdi = P.q.c.B ∧
    WP isa (.loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne) t
      fun t₂ => t₂.gpr .rdi = stackArg s 2 ∧
        WP isa (.block [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) t₂ (PPHead s)

/-- After `zeroPre`. -/
def C3 (P : PCPub) (t : State) : Prop :=
  ∃ s, PRel P s ∧ t.gpr .rdi = P.q.c.B ∧ WP isa (.block [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) t
    (PPHead s)

theorem zero_ct : RelCT isa (Two C2) PrivPre.zeroPre (Two C3) := by
  unfold PrivPre.zeroPre
  refine RelCT.seq (two_piece (Ψ := C2b) [.rdi, .rsi] (fun P s₁ s₂ ⟨σ₁, h₁, c₁⟩ ⟨σ₂, h₂, c₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [c₁.1, c₂.1, h₁.2.2.2.2.1, h₂.2.2.2.2.1]
      · rw [c₁.2.1, c₂.2.1, h₁.2.2.1, h₂.2.2.1]) (by taint_decide) ?_)
    (two_post (two_taint [.rsi, .rcx, .rdi] (fun P s₁ s₂ ⟨_, _, a₁, b₁, d₁, _⟩ ⟨_, _, a₂, b₂, d₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [d₁, d₂]) (by taint_decide))
      fun P t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t₂ ⟨hdi, hr⟩ => ⟨s, hs, hdi.trans hs.2.2.2.2.1, hr⟩)
  rintro P t ⟨s, hs, hdi, hsi, hsc, hO, hw⟩
  have hn := hsc.nowrap
  have c := ppCtx_of hs.1
  have hZ := c.hZ
  have hk1 := c.hk1
  have hL := c.hL
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords] at hL
  unfold PrivPre.zeroPre at hw
  rw [WP.seq_iff] at hw
  have hl : InRegions (t.rd ++ t.wr) (off (stackArg s 2) (8 * sOut)) 8 := hsc.ld (by unfold sOut sFn; omega)
  refine WP.mono (WP.and hw (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = s.gpr .rdi ∧
      t'.gpr .rcx = BitVec.ofNat 64 ((s.gpr .rsi).toNat * 8))
    (by xrun [State.ea, hdr, hdi, hdrOff, hl, hO, hsi, eight_w _ (ofNat_toNat_self (s.gpr .rsi)).symm]) rfl))
    fun t' ⟨hw', ⟨hsi', hcx'⟩, k⟩ => ⟨s, hs, by rw [hsi', hs.2.2.2.2.2.2.2.1], by rw [hcx', hs.2.2.2.1],
      by rw [k.gpr (by decide), hdi, hs.2.2.2.2.1], hw'⟩

/-- After the reloads. -/
def C4 (P : PCPub) (t : State) : Prop := ∃ s, PRel P s ∧ PPHead s t

/-- After the modulus' check. -/
def C5 (P : PCPub) (t : State) : Prop :=
  ∃ s t₁, PRel P s ∧ PPHead s t₁ ∧ t.mem = t₁.mem ∧ Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid P.q.c.N P.q.c.k)

theorem check_ct : RelCT isa (Two C3)
    (.block (([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid)) (Two C5) := by
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := C4) [.rdi] (fun P s₁ s₂ ⟨_, _, a₁, _⟩ ⟨_, _, a₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) (by taint_decide)
      fun P t ⟨s, hs, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩)
    (two_piece [.rdx, .rcx] (fun P s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx, c₁.2.2.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.2.2.1]
      · rw [h₁.rcx, h₂.rcx, c₁.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.1]) (by taint_decide) ?_))
  rintro P t ⟨s, hs, h⟩
  have c := ppCtx_of hs.1
  have hnb := Src.of_head (t := t) c.hnb (by rw [bytesAt_length]; exact c.hon) h.frame h.keep.2.1 h.keep.2.2
  obtain ⟨-, -, -, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, hn⟩ := id hs
  refine WP.mono (invalid_ok h.rdx h.rcx c.hk1 c.hk2 (bytesAt_length _ _ _) (fun i hi => hnb.rd i (by
    rw [bytesAt_length]; exact hi)) (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
  rw [hz, CrtPub.N, ← hn, hk]

theorem fail_ct : RelCT isa (Two fun P t => C5 P t ∧ isa.eval .ne t = some true) fail fun _ _ => True := by
  unfold fail
  have pin : ∀ P t, (C5 P t ∧ isa.eval .ne t = some true) → t.gpr .rdi = P.q.c.B := fun P t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ =>
    (k.gpr (by decide)).trans (h.rdi.trans hs.2.2.2.2.1)
  refine RelCT.seq (two_piece (Ψ := fun (P : PCPub) t => t.gpr .rsi = P.q.c.op ∧
      t.gpr .rcx = BitVec.ofNat 64 P.q.c.k ∧ t.gpr .rdi = P.q.c.B) [.rdi]
    (fun P s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [pin P s₁ h₁, pin P s₂ h₂]) (by taint_decide) ?_)
    (two_taint [.rsi, .rcx, .rdi] (fun P s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
  rintro P t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩
  have c := ppCtx_of hs.1
  have hpre := ppPre_of c h hm k
  have hn := hpre.scr.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (stackArg s 2) (8 * i)) 8 := fun i hi =>
    hpre.scr.ld (by omega)
  refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = s.gpr .rdi ∧
      t'.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat) (by
    xrun [State.ea, hdr, hpre.rdi, hdrOff, hl sOut (by decide), hl sK (by decide), hpre.hO, hpre.hK]) rfl)
    fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨by rw [hsi, hs.2.2.2.2.2.2.2.1], by rw [hcx, hs.2.2.2.2.2.2.1],
      (k'.gpr (by decide)).trans (hpre.rdi.trans hs.2.2.2.2.1)⟩

/-- `main`'s stages from the modulus' check, for a valid modulus. -/
theorem toSX {P : PCPub} {t : State} (h : C5 P t ∧ isa.eval .ne t = some false) : SX R0 P.q t := by
  obtain ⟨⟨s, t₁, hs, hh, hm, k, hz⟩, he⟩ := h
  have c := ppCtx_of hs.1
  have hpre := ppPre_of c hh hm k
  have hv : Spec.Rsa.modulusValid P.q.c.N P.q.c.k = true := by simp only [eval, hz] at he; simpa using he
  obtain ⟨-, -, hsi, hL8, hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql, hnb⟩ := hs
  have kk := hh.keep.trans k
  refine ⟨t, List.replicate (s.gpr .rcx).toNat 0, Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat,
    Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat,
    Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat, List.replicate (s.gpr .r9).toNat 0, ?_, hv, rfl,
    ?_, ?_, ?_, ?_⟩
  · rw [← hnb, ← hB, ← hZ, ← hk, ← hop, ← hnp, ← hip, ← hpp, ← hqp, ← hdpp, ← hdqp, ← hqip, ← hpl, ← hql]
    exact hpre
  · rw [kk.2.2, ← hop, ← hL8]; exact c.hpreR
  · rw [← hop, ← hL8]; exact c.hwrap
  · rw [← hop, ← hL8, ← hB, ← hZ]; exact c.hS
  · rw [← hL8, preWords c, CrtPub.w, ← hk, ← hpl, ← hql]; omega

/-- `vg_rsa_private_precompute` leaks the same in runs that agree on the
public data. -/
theorem code_ct (M : Mont) : RelCT isa (Two PRel) (PrivPre.code M.mm) fun _ _ => True := by
  unfold PrivPre.code
  refine RelCT.seq entry_ct (RelCT.seq zero_ct (RelCT.seq check_ct (two_ite (fun P s₁ s₂ h₁ h₂ => ?_)
    fail_ct ((main_ct M).mono (fun _ _ h => two_bind (fun P t₁ t₂ h₁ h₂ => ⟨P.q, toSX h₁, toSX h₂⟩) h)
      fun _ _ h => h))))
  obtain ⟨_, _, _, _, _, _, z₁⟩ := h₁
  obtain ⟨_, _, _, _, _, _, z₂⟩ := h₂
  simp only [eval, z₁, z₂]

/-- The public data of a state. -/
def pcPubOf (s : State) : PCPub :=
  ⟨⟨⟨stackArg s 2, (stackArg s 3).toNat * 8, (s.gpr .rcx).toNat, s.gpr .rdi, s.gpr .rdx, s.gpr .rdi, s.gpr .r8,
    stackArg s 0, s.gpr .r8, stackArg s 0, s.gpr .rdi, (s.gpr .r9).toNat, (stackArg s 1).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat⟩, (s.gpr .rsi).toNat * 8⟩, s.gpr .rsp, s.gpr .rsi⟩

/-- `vg_rsa_private_precompute` is constant time but for `n`. -/
theorem code_constantTime (M : Mont) : ConstantTime isa ppContract.pre ppContract.pub (PrivPre.code M.mm) := by
  refine RelCT.constantTime ((code_ct M).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨pcPubOf s₁, ?_, ?_⟩)
    fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .rsp (by decide), r .rsi (by decide), by rw [r .rsi (by decide)]; rfl, a2.symm,
      by rw [← a3]; rfl, by rw [r .rcx (by decide)]; rfl, r .rdi (by decide), r .rdx (by decide),
      r .rdi (by decide), r .r8 (by decide), a0.symm, r .r8 (by decide), a0.symm, r .rdi (by decide),
      by rw [r .r9 (by decide)]; rfl, by rw [← a1]; rfl, hn.symm⟩

end VG.Proof.Bignum.X86_64.PrivPre
