module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub

import VerifiedGarbage.Proof.Framework.Mem

/-! # Scrubbing where the residue analysis follows the code, else wiping the whole stack -/

/-!
`withScrubOrAll` scrubs an instance of a generic function after its residue
analysis where it has one, and otherwise with every granule of its stack
wiped (`Scrub.withScrubAll`). `withScrubAllM` wipes every granule too, and
clears the vector registers at the level `withScrub` would (`levelFor`):
code that saves, loads and restores MXCSR around the multiplications of
Intel's MCDT list (`mxClass`), but writes no register only AVX-512 has, is
cleared below the level `evex`, and so needs no AVX-512 feature.

Code that loads MXCSR only between `mxcsrSave` and `mxcsrRestore`
(`ctlOk`), but leaves in it what it held on entry on some paths and that but
for its reserved bits on others (an early return before any such pair), is
followed by `mxNorm`, which leaves MXCSR's control bits alone, as the level
`evex` of `scrub` does (`mxFix`): MXCSR on return is then a function of
MXCSR on entry (`norm_mxFun`), and `withScrubAllR` clears that code below the
level `evex` too.
-/

@[expose] public section

namespace VG.X86_64.RScrub

open VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- `r` scrubbed after the residue analysis `a` where an instance of a
generic function has one (`withScrub`), and otherwise with every granule of
its stack wiped (`Scrub.withScrubAll`): for the instances whose code the
analysis does not follow, of a function with a small stack. -/
def withScrubOrAll {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (pubs : List (Nat × Nat × Nat)) (hpub : PubOk r.contract pubs)
    (a : Option (Analysed api.sig r.stack pubs r.code)) : Registration api target :=
  match a with
  | some a => withScrub r hpost pubs hpub (some a)
  | none => withScrubAll r hpost

/-! ## MXCSR's control bits alone -/

/-- `ctlOk`, computed (with `restoresC` and `List.all`), for the emitter. -/
def ctlOkC : Prog isa → Bool
  | .block is => is.all fun i => !loadsMxcsr i
  | .seq a b => restoresC a b || (ctlOkC a && ctlOkC b)
  | .ite _ t e => ctlOkC t && ctlOkC e
  | .loop b _ => ctlOkC b
  | .call _ b => ctlOkC b
  | .frame i b j => !loadsMxcsr i && ctlOkC b && !loadsMxcsr j
  | .icall i _ b n => !loadsMxcsr i && ctlOkC b && ctlOkC n

theorem restores_of_C {a b : Prog isa} (h : restoresC a b = true) : restores a b = true := by
  obtain ⟨m, m', r, mid, rfl, rfl, hk⟩ := restoresC_eq h
  simp only [restores, mxcsrSave, mxcsrRestore, saveOp, restoreOp, BEq.rfl, Bool.true_and,
    Code.allInstrs_eq, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  exact hk

theorem ctlOk_of_C {c : Prog isa} (h : ctlOkC c = true) : ctlOk c = true := by
  induction c with
  | block is => exact (KList.all_eq _ _).trans h
  | seq a b iha ihb =>
    simp only [ctlOkC, Bool.or_eq_true, Bool.and_eq_true] at h
    simp only [ctlOk, Bool.or_eq_true, Bool.and_eq_true]
    rcases h with h | h
    · exact .inl (restores_of_C h)
    · exact .inr ⟨iha h.1, ihb h.2⟩
  | ite _ _ _ iht ihe =>
    simp only [ctlOkC, Bool.and_eq_true] at h
    simp only [ctlOk, iht h.1, ihe h.2, Bool.and_self]
  | loop _ _ ih => exact ih h
  | call _ _ ih => exact ih h
  | frame _ _ _ ih =>
    simp only [ctlOkC, Bool.and_eq_true] at h
    simp only [ctlOk, h.1.1, h.2, ih h.1.2, Bool.and_self]
  | icall _ _ _ _ ihb ihn =>
    simp only [ctlOkC, Bool.and_eq_true] at h
    simp only [ctlOk, h.1.1, ihb h.1.2, ihn h.2, Bool.and_self]

/-- `r11` zeroed, then MXCSR with its status flags and reserved bits cleared
(`mxFix` of the level `evex`, which expects `r11` zero): what is left in it
is a function of its control bits, which code that `ctlOk` accepts keeps. -/
def mxNorm : Prog isa := .seq (.block [zeroR .r11]) (mxFix .evex)

theorem mxNorm_run (u : State) (h16 : 16 ≤ (u.gpr .rsp).toNat) :
    ∃ m', Exec isa mxNorm u (mxTr .evex (u.gpr .rsp))
        { clearedG [.r11] u with mem := m', mxcsr := u.mxcsr &&& 0xFFC0 } ∧
      ∀ x, ¬ (x - (u.gpr .rsp - 16#64)).toNat < 8 → m' x = u.mem x := by
  have h₁ := execBlock_gprs [.r11] (by simp) u
  have hsp : (clearedG [.r11] u).gpr .rsp = u.gpr .rsp := by simp [clearedG]
  obtain ⟨m', he, hm⟩ := mxFix_run .evex (clearedG [.r11] u) (fun _ => by rw [hsp]; exact h16)
    (fun _ => by simp [clearedG])
  rw [hsp] at he hm
  have e := Exec.seq (M := isa) (.block h₁) he
  rw [List.nil_append] at e
  exact ⟨m', e, fun x hx => hm x fun ⟨_, h⟩ => hx h⟩

theorem mxNorm_mx {u u' : State} {t : List Leak} (h : Exec isa mxNorm u t u') :
    u'.mxcsr = u.mxcsr &&& 0xFFC0 := by
  by_cases h16 : 16 ≤ (u.gpr .rsp).toNat
  · obtain ⟨m', e, -⟩ := mxNorm_run u h16
    obtain ⟨-, rfl⟩ := Exec.det h e
    rfl
  · exfalso
    cases h with | seq h₁ h₂ =>
    rw [Exec.block_iff, show [zeroR .r11] = [Reg.r11].map zeroR from rfl, execBlock_gprs [.r11] (by simp)] at h₁
    simp only [Option.some.injEq, Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    cases h₂ with | frame hp _ _ =>
    simp only [isa, push] at hp
    split at hp
    · rename_i hc; exact h16 (by simpa [clearedG] using hc.2.2.2)
    · cases hp

/-- Code that `ctlOk` accepts, followed by `mxNorm`, leaves in MXCSR a
function of MXCSR on entry. -/
theorem norm_mxFun {c : Prog isa} (hc : ctlOk c = true) :
    ∃ f : BitVec 32 → BitVec 32, ∀ s t s', Exec isa (.seq c mxNorm) s t s' → s'.mxcsr = f s.mxcsr :=
  ⟨fixMx .evex, fun s t s' h => by
    cases h with | seq h₁ h₂ =>
    rw [mxNorm_mx h₂]
    exact fixMx_congr .evex rfl (Exec.ctl hc h₁)⟩

/-- Code verified against a contract whose `stack` bytes below the stack
pointer, at least 16, no buffer overlaps, followed by `mxNorm`: verified
against the same contract, if its postcondition reads the memory on return
only within the buffers (`hpost`). -/
theorem Verified.norm {k : Contract isa} {c : Prog isa} {stack rb : Nat}
    (h : Verified target c k) (h16 : 16 ≤ stack)
    (hk : ∀ s, k.pre s → stack ≤ (s.gpr .rsp).toNat ∧ ∀ r ∈ s.rd ++ s.wr,
      (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Disjoint r)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp) (hpost : PostOut k rb) :
    Verified target (.seq c mxNorm) k := by
  obtain ⟨hcor, hct, hsat⟩ := h
  have run : ∀ s t u, k.pre s → Exec isa c s t u →
      abiPreserved s u ∧ k.post s u ∧ u.gpr .rsp = s.gpr .rsp ∧ 16 ≤ (u.gpr .rsp).toNat := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, hp⟩ := hcor s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
    exact ⟨ha, hp, hr, by rw [hr]; have := (hk s hs).1; omega⟩
  -- `mxNorm` stores only below the stack pointer, within the `stack` bytes.
  have inS : ∀ s, k.pre s → ∀ x, (x - (s.gpr .rsp - 16#64)).toNat < 8 →
      (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 := by
    intro s hs x hx
    have hl := (hk s hs).1
    have hsl : stack < 2 ^ 64 := Nat.lt_of_le_of_lt hl (s.gpr .rsp).isLt
    simp only [Region.Contains]
    generalize s.gpr .rsp = p at hx hl
    bv_omega
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, u, he, -⟩ := hcor s hs
    obtain ⟨ha, hq, hr, hl⟩ := run s t u hs he
    obtain ⟨m', en, hm⟩ := mxNorm_run u hl
    rw [hr] at hm
    refine ⟨_, _, .seq he en, ⟨fun r hr' => ?_, ?_, ?_⟩, ?_⟩
    · have h1 : r ≠ .r11 := by revert hr'; revert r; decide
      simp only [clearedG, List.mem_singleton, h1, ↓reduceIte]
      exact ha.1 r hr'
    · rw [← ha.2.1]
      apply Mem.readW_congr
      intro i hi
      apply hm
      simp only [Nat.reduceDiv] at hi
      generalize s.gpr .rsp = p
      bv_omega
    · show (u.mxcsr &&& 0xFFC0#32).extractLsb' 6 10 = _
      rw [← ha.2.2]; exact fixMx_ctl .evex u.mxcsr
    · refine hpost s u _ hs hq (fun x ⟨r, hr', hx⟩ => hm x fun h => ?_) rfl
      exact (hk s hs).2 r hr' x (inS s hs x h) hx
  · cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨-, -, hr₁, hl₁⟩ := run s₁ _ _ h₁ a₁
    obtain ⟨-, -, hr₂, hl₂⟩ := run s₂ _ _ h₂ a₂
    obtain ⟨_, en₁, -⟩ := mxNorm_run _ hl₁
    obtain ⟨_, en₂, -⟩ := mxNorm_run _ hl₂
    obtain ⟨rfl, -⟩ := Exec.det b₁ en₁
    obtain ⟨rfl, -⟩ := Exec.det b₂ en₂
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, hr₁, hr₂, hpub _ _ hp]

/-- `r`, its code followed by `mxNorm`: for code that `ctlOk` accepts, which
then leaves in MXCSR a function of MXCSR on entry (`norm_mxFun`). -/
def withNorm {api : Api} (r : Registration api target) (h16 : 16 ≤ r.stack)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hw : r.written = []) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := .seq r.code mxNorm
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    rw [e] at hv hp ⊢
    have hA := ScrubAbi.of r.consts api.sig r.tables api.pubMode
    exact Verified.norm hv h16
      (fun s hs => ⟨((contract_pre_scrub hA hs).1.resolve_left (by omega)),
        fun r' hr' => ((contract_pre_scrub hA hs).2 r' hr').2 (by omega)⟩)
      (fun _ _ hp => contract_pub_rsp hA hp) hp
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := by simp only [Code.all, r.spSafe, Bool.true_and]; rfl
  written := r.written
  writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith

/-- `r`, scrubbed as `scrubRegE` does below the level `evex`, for code that
leaves in MXCSR a function of MXCSR on entry (`hmx`). -/
def scrubRegF {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : ∃ f : BitVec 32 → BitVec 32, ∀ s t s', Exec isa r.code s t s' → s'.mxcsr = f s.mxcsr)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack))
    (hw : r.written = []) (hne : v ≠ .evex) : Registration api target :=
  have main : Verified target (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code) r.contract ∧
      NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code) r.contract
        (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    have hr := hres
    rw [e] at hv hp hr ⊢
    have hrb' := hrb
    rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
    have he : EvexReg r.code v ks r.stack := evexReg_of_ne hne
    exact Verified.scrubM (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
      (chunks_sum r.stack) hst (chunks_valid h8)
      (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun _ => hmx) hrb' hp hr (tailOk_of _ _ _)
      (xs_of _ _) he.1 he.2 (gs_of _ _)
  { suffix := r.suffix
    consts := r.consts
    tables := r.tables
    stack := r.stack
    code := scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code
    contract := r.contract
    verified := main.1
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe v _ _ _ _ _ _ (tailOk_of 0 r.code ks).psOk (tailOk_of 0 r.code ks).gsOk r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith
    residue := some ⟨main.2⟩ }

/-- `r` with every granule of its stack wiped and the vector registers
cleared at the level `levelFor` of its code, for code that leaves in MXCSR a
function of MXCSR on entry (`hmx`), if `scrubRegF`'s side conditions hold and
the clearing needs no CPU feature its code does not; otherwise `r` itself. -/
def withScrubAllF {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hmx : ∃ f : BitVec 32 → BitVec 32, ∀ s t s', Exec isa r.code s t s' → s'.mxcsr = f s.mxcsr) :
    Registration api target :=
  let v := levelFor r.code
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if h8 : r.stack % 8 = 0 then
  if hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
    let r' := scrubRegF r v (allKs (chunks r.stack)) hd hst h8 hlv hmx hrb hpost (resOk_all _ _ h8) hw
      (levelFor_ne _)
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r
  else r else r else r else r else r else r

/-- `r` with every granule of its stack wiped and the vector registers
cleared at the level `levelFor` of its code (`withScrubAllF`): if it leaves
in MXCSR a function of MXCSR on entry (`mxClass`), or else, if `ctlOk`
accepts it, followed by `mxNorm` (`withNorm`, `norm_mxFun`); otherwise `r`
itself. -/
def withScrubAllR {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  if hmx : (mxClass r.code).isSome = true then withScrubAllF r hpost (mxFun_of hmx) else
  if h16 : 16 ≤ r.stack then
  if hw : r.written = [] then
  if hc : ctlOkC r.code = true then
    let r' := withScrubAllF (withNorm r h16 hpost hw) hpost (norm_mxFun (ctlOk_of_C hc))
    if r'.residue.isSome then r' else r
  else r else r else r

/-- `withScrubAllR` where it applies, else `Scrub.withScrubAll`. -/
def withScrubAllM {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  let r' := withScrubAllR r hpost
  if r'.residue.isSome then r' else withScrubAll r hpost

end VG.X86_64.RScrub
