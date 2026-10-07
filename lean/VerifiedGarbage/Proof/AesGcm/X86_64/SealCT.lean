import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. After the entry, which loads
`work` from the stack first, both runs go through the same pieces with the
same public data (`oneAad_rel`, `oneBlocksE_rel`, `oneCrypt_rel`, `oneTag_rel`),
and copy the tag to the same address, `tag`, which correctness says is still
on the stack (`sealRun_ok`, `tagOut_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

/-- `oneAad`'s precondition, after the entry. -/
theorem OneEntry.aadPre {M : Gcm.X86_64.Stitch.CtxMode} {s₀ s : State} {k : Nat} {Ctx W SP Np A D : Addr}
    {nl al n R : Nat} (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (E : OneEntry s₀ Ctx W SP A D n s) (hNp : s₀.gpr .rdx = Np)
    (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) (hR : (s₀.gpr .rsi).toNat = R) :
    OneS M Ctx W SP R A al D n none s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl :=
  ⟨⟨E.env, hR ▸ E.rounds, E.aad, by rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len,
    C.aad.of_eq E.rd E.wr, C.data.of_eq E.rd E.wr, fun _ h => (nomatch h),
    X.keep E.rd E.wr E.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact X.cw.sub_right (Lay.wSub (by decide))⟩, by rw [E.r12, hNp],
    by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq], C.nonce.of_eq E.rd E.wr⟩

theorem one_pub {k : Nat} {s₀ s₀' : State} (hq : Proof.AesGcm.onePub k s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- `e; (m; (o; f))`, related as `e; ((m; o); f)`. -/
theorem rel_reassoc_mid {P Q : State → State → Prop} {e m o f : Prog isa}
    (h : RelCT isa P (.seq e (.seq (.seq m o) f)) Q) : RelCT isa P (.seq e (.seq m (.seq o f))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq m₁ e₁ => cases e₁ with | seq o₁ f₁ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq m₂ e₂ => cases e₂ with | seq o₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq x₁ (.seq (.seq m₁ o₁) f₁)) (.seq x₂ (.seq (.seq m₂ o₂) f₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `x; (a; (b; (c; ((d; o); f))))`, related as `x; ((a; (b; (c; d))); (o; f))`. -/
theorem rel_reassoc_seal' {P Q : State → State → Prop} {x a b c d o f : Prog isa}
    (h : RelCT isa P (.seq x (.seq (.seq a (.seq b (.seq c d))) (.seq o f))) Q) :
    RelCT isa P (.seq x (.seq a (.seq b (.seq c (.seq (.seq d o) f))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with
    | seq c₁ e₁ => cases e₁ with | seq e₁ f₁ => cases e₁ with | seq d₁ o₁ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with
    | seq c₂ e₂ => cases e₂ with | seq e₂ f₂ => cases e₂ with | seq d₂ o₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq x₁ (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) (.seq o₁ f₁)))
    (.seq x₂ (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) (.seq o₂ f₂)))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `seal` with any code `mid` after the entry that leaves what `sealRun_ok`
does (`hmid`) and that two runs go through alike (`hrel`). -/
theorem sealM_relOf {M : Gcm.X86_64.Stitch.CtxMode} {mid : Prog isa} {s₀ s₀' : State}
    (hp : (Proof.AesGcm.sealX86_64M M).pre s₀) (hp' : (Proof.AesGcm.sealX86_64M M).pre s₀')
    (hq : Proof.AesGcm.sealX86_64.pub s₀ s₀')
    (hmid : ∀ {s : State} {Ctx W SP Np A D : Addr} {nl al n : Nat} {s₁ : State},
      OneCtx s 4 Ctx W SP Np A D nl al n → CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s →
      OneEntry s Ctx W SP A D n s₁ → s.gpr .rdx = Np → (s.gpr .rcx).toNat = nl → (s.gpr .r9).toNat = al →
      WP isa mid s₁ (SealRunPost s Ctx W SP Np A D nl al n))
    (hrel : ∀ {Ctx W SP Np A D : Addr} {nl al n R : Nat},
      OneCtx s₀ 4 Ctx W SP Np A D nl al n → OneCtx s₀' 4 Ctx W SP Np A D nl al n →
      CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀ → CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀' →
      s₀.gpr .rdx = Np → (s₀.gpr .rcx).toNat = nl → (s₀.gpr .r9).toNat = al → (s₀.gpr .rsi).toNat = R →
      s₀'.gpr .rdx = Np → (s₀'.gpr .rcx).toNat = nl → (s₀'.gpr .r9).toNat = al → (s₀'.gpr .rsi).toNat = R →
      RelCT isa (fun s₁ s₂ => True ∧ OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂) mid
        fun _ _ => True) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block (oneEntry 32)) (.seq mid (.seq (.block (tagOut (at_ .rsp 24))) (.block restore))))
      fun _ _ => True := by
  have C := (OneCtx.ofSeal hp.1 M.ge).1
  have C' := (OneCtx.ofSeal hp'.1 M.ge).1
  have X := CtxExt.ofSeal hp.1 hp.2
  have X' := CtxExt.ofSeal hp'.1 hp'.2
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩ := hq'
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  have a₃ := qa 3 (by decide)
  simp only [Proof.AesGcm.arg] at a₀ a₁ a₂ a₃
  have ha₃ := C.args 3 (by decide); have ha₃' := C'.args 3 (by decide)
  have hw32 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 32) 64 := a₃
  have hT₁ : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s₀ 2 := rfl
  have hT₂ : s₀'.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s₀ 2 := by rw [q₇, a₂]; rfl
  rw [← q₁, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₁, ← a₃] at C'
  rw [← q₁, ← q₇, ← a₀, ← a₁, ← a₃] at X'
  have hE : ∀ {s : State} (C : OneCtx s 4 (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .rdx) (s₀.gpr .r8)
      (stackArg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (stackArg s₀ 1).toNat),
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsp = s₀.gpr .rsp → s.gpr .r8 = s₀.gpr .r8 →
      stackArg s 0 = stackArg s₀ 0 → (stackArg s 1).toNat = (stackArg s₀ 1).toNat →
      s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s₀ 3 →
      InRegions (s.rd ++ s.wr) (s₀.gpr .rsp + BitVec.ofNat 64 32) 8 →
      WP isa (.block (oneEntry 32)) s
        (OneEntry s (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 1).toNat) :=
    fun C h₁ h₂ h₃ h₄ h₅ h₆ h₇ => oneEntry_ok (by decide) C h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hE₁ := hE C rfl rfl rfl rfl rfl rfl ha₃
  have hE₂ := hE C' q₁.symm q₇.symm q₅.symm a₀.symm (by rw [a₁]) (by rw [q₇, a₃]; rfl) (by rw [q₇]; exact ha₃')
  rw [oneEntry, List.append_assoc, List.append_assoc, List.append_assoc] at hE₁ hE₂
  rw [oneEntry, List.append_assoc, List.append_assoc, List.append_assoc]
  refine rel_reassoc_mid (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 3 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 3) (SP := s₀.gpr .rsp) (k := 32) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (one_pub hq) hw32 ha₃ ha₃' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  -- The address of `tag`, at `[SP + 24]`, after `mid`: by correctness.
  have dA := C.arg24 (by decide)
  have hW : ∀ {s₀'' s : State} (C : OneCtx s₀'' 4 (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .rdx)
      (s₀.gpr .r8) (stackArg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (stackArg s₀ 1).toNat),
      CtxExt M (s₀.gpr .rdi) (stackArg s₀ 3 + BitVec.ofNat 64 16) (stackArg s₀ 3) (s₀.gpr .rsp) (stackArg s₀ 0)
        (stackArg s₀ 1).toNat s₀'' →
      s₀''.gpr .rdx = s₀.gpr .rdx → (s₀''.gpr .rcx).toNat = (s₀.gpr .rcx).toNat →
      (s₀''.gpr .r9).toNat = (s₀.gpr .r9).toNat →
      s₀''.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s₀ 2 →
      OneEntry s₀'' (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 1).toNat s →
      WP isa mid s (TagAt (s₀.gpr .rdi) (stackArg s₀ 3 + BitVec.ofNat 64 16) (stackArg s₀ 3)
          (s₀.gpr .rsp) .rsp 24 (stackArg s₀ 2)) :=
    fun C X h₁ h₂ h₃ hT E => WP.mono (hmid C X E h₁ h₂ h₃) fun _ ⟨he, hrd, hwr, _, f, _⟩ => ⟨he, by
      rw [he.rsp, f.readW (r := ⟨s₀.gpr .rsp + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dA _ (.inl fun _ h => h)
        · exact dA _ (.inr (.inl fun _ h => h))
        · exact dA _ (.inr (.inr fun _ h => h))) (by decide), hT], by
      rw [he.rsp, hrd, hwr]; exact C.args 2 (by decide)⟩
  have m := rel_wp (hrel C C' X X' rfl rfl rfl rfl q₃.symm (by rw [q₄]) (by rw [q₆]) (by rw [q₂]))
    (fun _ _ h => h.2) (fun _ h => hW C X rfl rfl rfl hT₁ h) (fun _ h => hW C' X' q₃.symm (by rw [q₄]) (by rw [q₆]) hT₂ h)
  exact RelCT.seq m (tagOut_rel (b := .rsp) (d := 24) (by simp) ⟨_, by taint_decide⟩ (fun _ _ h => h.2))

/-- After the entry, the other instances' body in two runs: `oneAad`,
`oneBlocks`, `oneCrypt` and `oneTag 0`. -/
theorem sealRun_rel (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s₀ s₀' : State}
    {Ctx W SP Np A D : Addr} {nl al n R : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) :
    RelCT isa (fun s₁ s₂ => True ∧ OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
      (.seq (oneAad v.callees) (.seq (oneBlocks B.enc) (.seq (oneCrypt v.callees) (oneTag v.callees 0))))
      fun _ _ => True := by
  have L := C.lay
  have hDW := C.dE
  have hn := C.data.ok.lt
  have hDW' := C.dE.sub_left (Offset.sub_base D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (by omega))
  have a := (oneAad_rel v L hDW (T := none) (R := R) (Np := Np) (nl := nl)).mono
    (P' := fun (s₁ s₂ : State) => True ∧ OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
    (fun _ _ h => ⟨h.2.1.aadPre C X hNp hnl hal hR, h.2.2.aadPre C' X' hNp' hnl' hal' hR'⟩) fun _ _ h => h
  have bl := oneBlocksE_rel B L (R := R) (A := A) (al := al) (T := none) C.t_c C.t_w C.t_d C.sp24
  have t := oneTag_rel v L (M := M) (.inl rfl) hDW' (N := n) (R := R) (A := A) (al := al)
  exact (RelCT.seq a (RelCT.seq bl (RelCT.seq (oneCrypt_rel v L hDW') t))).mono (fun _ _ h => h)
    fun _ _ _ => trivial

theorem sealM_rel (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s₀ s₀' : State}
    (hp : (Proof.AesGcm.sealX86_64M M).pre s₀) (hp' : (Proof.AesGcm.sealX86_64M M).pre s₀')
    (hq : Proof.AesGcm.sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» (v.withBlk B)) fun _ _ => True :=
  rel_reassoc_seal' (sealM_relOf hp hp' hq (fun C X E hNp hnl hal => sealRun_ok v B C X E hNp hnl hal)
    fun C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' =>
      sealRun_rel v B C C' X X' hNp hnl hal hR hNp' hnl' hal' hR')

theorem sealM_ct (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    ConstantTime isa (Proof.AesGcm.sealX86_64M M).pre Proof.AesGcm.sealX86_64.pub («seal» (v.withBlk B)) :=
  ct_of_rel fun _ _ hp hp' hq => sealM_rel v B hp hp' hq

theorem seal_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.sealX86_64.pre Proof.AesGcm.sealX86_64.pub («seal» v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => sealM_rel v v.blkB ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq

end VG.Proof.AesGcm.X86_64
