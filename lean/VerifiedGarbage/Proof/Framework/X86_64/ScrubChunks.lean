module

public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
import VerifiedGarbage.Proof.Framework.CodeOnce

/-!
# x86-64 residue: wiping the stack in chosen chunks

`Scrub.scrubRegM` and `RScrub.withScrubRes` wipe the stack in
`chunks r.stack`, whose 16-byte granules end at the stack pointer on entry,
which is 8 off 16: every 16-byte store of the wipe is unaligned, and one in
four of them splits a cache line. The same, for any chunks `cs` summing to
the stack: a chunk of 8 bytes at the top puts the granules of the chunk
below it 16 bytes aligned (`scrubRegMC`, `withScrubResC`).
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

open VG.X86_64 VG.X86_64.Residue

/-- `scrubCodeE_noResidue`, below the level `evex`, with the stack wiped in
the chunks `cs` (from the top) rather than `chunks r.stack`: each chunk's
16-byte granules end at its top, so a chunk of 8 bytes at the top puts
those of the chunks below it 16 bytes aligned, the stack pointer on entry
being 8 off 16. -/
theorem scrubCodeMC_noResidue {api : Api} (r : Unscrubbed api target) (v : VecLevel) (ks cs : List Nat)
    (hcs : cs.sum = r.stack) (hcv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks cs) (hne : v ≠ .evex) (hic : tablesCall r.code r.tables = true) :
    NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code) r.contract
      (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hr := hres
  rw [e] at hv hp hr ⊢
  have hrb' := hrb
  exact (Verified.scrubM (ScrubAbi.of r.consts api.sig r.tables) hv (SpSafe.of_all r.spSafe) hd
    hcs hst hcv
    (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun _ => MxSame.of_fun (mxFun_of hmx)) hrb' hp hr
    (tailOk_of _ _ _) (xs_of _ _) (fun e => absurd e hne) (fun _ _ e => absurd e hne) (gs_of _ _)).2 (tablesCall_syms hic rfl)

/-- `scrubRegM`, with the stack wiped in the chunks `cs` (`scrubCodeMC_noResidue`). -/
def scrubRegMC {api : Api} (r : Unscrubbed api target) (v : VecLevel) (ks cs : List Nat)
    (hcs : cs.sum = r.stack) (hcv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks cs)
    (hw : r.written = []) (hne : v ≠ .evex) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code
  contract := r.contract
  unscrubbed := !(tablesCall r.code r.tables)
  verified := .abi (cs := r.consts) (sig' := api.sig) (ts := r.tables) <| Verification.ofBool (tablesCall r.code r.tables) (by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    have hr := hres
    rw [e] at hv hp hr ⊢
    have hrb' := hrb
    exact (Verified.scrubM (ScrubAbi.of r.consts api.sig r.tables) hv (SpSafe.of_all r.spSafe) hd
      hcs hst hcv
      (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun _ => MxSame.of_fun (mxFun_of hmx)) hrb' hp hr
      (tailOk_of _ _ _) (xs_of _ _) (fun e => absurd e hne) (fun _ _ e => absurd e hne) (gs_of _ _)).1) (fun hic => scrubCodeMC_noResidue r v ks cs hcs hcv hd hst hlv hmx hrb hpost hres hne hic)
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrub_spSafe v _ _ _ _ _ _ (tailOk_of 0 r.code ks).psOk (tailOk_of 0 r.code ks).gsOk r.spSafe
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  -- As `scrubRegE`'s: for code that calls indirectly only its tables' functions.

end VG.X86_64.Scrub

namespace VG.X86_64.RScrub

open VG.X86_64 VG.X86_64.Taint VG.X86_64.RTaint VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- `withScrubRes`, with the stack wiped in the chunks `cs` (from the top;
`Scrub.scrubRegMC`), which `hcs` and `hcv` check. -/
def withScrubResC {api : Api} (r : Unscrubbed api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (ks cs : List Nat) (hres : ResOk r.code r.contract r.stack ks cs) : Registration api target :=
  let v := levelFor r.code
  if hcs : cs.sum = r.stack then
  if hcv : cs.all (fun b => decide (0 < b ∧ b < 4096 ∧ b % 8 = 0)) = true then
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if hlv : r.code.allOnce (fun i => decide (i.vecLevelR ≤ v.level)) = true then
  if hmx : (mxClassOnce r.code).isSome = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
    scrubRegMC r v ks cs hcs (fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb)) hd hst
      ((Code.allOnce_eq _ r.code).symm.trans hlv) (mxClassOnce_eq r.code ▸ hmx) hrb hpost hres hw (levelFor_ne _)
  else r.registration else r.registration else r.registration else r.registration
  else r.registration else r.registration else r.registration else r.registration

/-- `Scrub.resOk_all`, for any chunks `cs` of the stack: with every granule
of the stack wiped, `ResOk` asks nothing of the code. -/
theorem resOk_allC (c : Prog isa) (k : Contract isa) {stack : Nat} {cs : List Nat}
    (h8 : ∀ b ∈ cs, b % 8 = 0) (hs : cs.sum = stack) : ResOk c k stack (allKs cs) cs := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ _ _ _ _ _ _ _ _ x hx hn
  exact absurd (wcov_all h8 (by rw [hs]; exact hx)) hn

/-- `r` with every granule of its stack wiped, in the chunks `cs` (from the
top; `withScrubResC`): with an 8-byte chunk at the top, every 16-byte store
of the wipe is aligned. `r` itself where a side condition fails. -/
def withScrubAllC {api : Api} (r : Unscrubbed api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (cs : List Nat) : Registration api target :=
  if h8 : cs.all (fun b => b % 8 == 0) = true then
  if hs : cs.sum = r.stack then
    withScrubResC r hpost (allKs cs) cs
      (resOk_allC _ _ (fun b hb => by have := List.all_eq_true.mp h8 b hb; simpa using this) hs)
  else r.registration else r.registration

/-- `scrubRegF`, with the stack wiped in the chunks `cs` (from the top)
rather than `chunks r.stack`, which `hcs` and `hcv` check: for code that
leaves the same MXCSR in two runs along the same trace (`hmx`), at any
level, with no `mxFix`. -/
def scrubRegFC {api : Api} (r : Unscrubbed api target) (v : VecLevel) (ks cs : List Nat)
    (hcs : cs.sum = r.stack) (hcv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : MxSame r.code)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks cs)
    (hw : r.written = []) (hxe : v = .evex → ∀ x, x ∈ xsOf r.code ks) : Registration api target :=
  have main : Verified target (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code .avx) r.contract ∧
      (tablesCall r.code r.tables = true →
        NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
          (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code .avx) r.contract
          (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    have hr := hres
    rw [e] at hv hp hr ⊢
    have hrb' := hrb
    have h := Verified.scrubM (f := .avx) (ScrubAbi.of r.consts api.sig r.tables) hv
      (SpSafe.of_all r.spSafe) hd hcs hst hcv
      (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun _ => hmx) hrb' hp hr (tailOk_of _ _ _)
      (xs_of _ _) hxe (fun _ _ e => absurd e (by decide)) (gs_of _ _)
    exact ⟨h.1, fun hic => h.2 (tablesCall_syms hic rfl)⟩
  { suffix := r.suffix
    consts := r.consts
    tables := r.tables
    stack := r.stack
    code := scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code .avx
    contract := r.contract
    -- As `scrubRegE`'s: for code that calls indirectly only its tables' functions.
    unscrubbed := !(tablesCall r.code r.tables)
    verified := .abi (cs := r.consts) (sig' := api.sig) (ts := r.tables) <| Verification.ofBool (tablesCall r.code r.tables) main.1 main.2
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe v _ _ _ _ _ _ (tailOk_of 0 r.code ks).psOk (tailOk_of 0 r.code ks).gsOk r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith }

/-- `withScrubAllR`, with the stack wiped in the chunks `cs` (from the top;
`scrubRegFC`): `r` with every granule of its stack wiped and the vector
registers cleared at the level `levelForE` of its code, if every `ldmxcsr`
in it loads what `Mx.mx` follows, the side conditions hold and the clearing
needs no CPU feature its code does not; otherwise `r` itself. With an 8-byte
chunk at the top, every 16-byte store of the wipe is aligned, and at every
level but `sse` it stores 32 bytes at a time. -/
def withScrubAllRC {api : Api} (r : Unscrubbed api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (cs : List Nat) : Registration api target :=
  let v := levelForE r.code
  if hmx : (Mx.mxOnce r.code []).isSome = true then
  if hcs : cs.sum = r.stack then
  if hcv : cs.all (fun b => decide (0 < b ∧ b < 4096 ∧ b % 8 = 0)) = true then
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if hlv : levelLeROnce v.level r.code = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
  if hx : v = .evex → noVec r.code = false then
    have hcv' : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0 :=
      fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb)
    let r' := scrubRegFC r v (allKs cs) cs hcs hcv' hd hst ((Code.allOnce_eq _ r.code).symm.trans hlv)
      (Mx.mxSame_of (Mx.mxOnce_eq r.code [] ▸ hmx)) hrb hpost
      (resOk_allC _ _ (fun b hb => (hcv' b hb).2.2) hcs) hw
      (fun e x => by unfold xsOf; rw [show r.code.all (fun i => !writesVec i) = false from hx e]; exact mem_xregs x)
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r.registration
  else r.registration else r.registration else r.registration else r.registration
  else r.registration else r.registration else r.registration else r.registration
  else r.registration

end VG.X86_64.RScrub
